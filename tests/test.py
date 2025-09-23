#!/usr/bin/env python3
import json
import os
import pwd
import re
import shutil
import subprocess
import tempfile
import time
import unittest
import sys

from pathlib import Path
from typing import Callable, TypeAlias, TypedDict, Union

class Device(TypedDict):
    major: int
    minor: int
class Parent(TypedDict, total=False):
    pid: int
    comm: str
    exe: str
class Event(TypedDict, total=False):
    timestamp: str
    comm: str
    pid: int
    uid: int
    gid: int
    types: str
    device: Device
    inode: int
    path: str
    exe: str
    parents: list[Parent]
    path_raw: list[int]
    comm_raw: list[int]
    parsed_from_text_log: bool
Pred: TypeAlias = Callable[[Event], bool]

TESTDIR = Path(__file__).parent.resolve()
ROOTDIR = TESTDIR.parent.resolve()

exe = subprocess.check_call

# check if root fs is btrfs
root_is_btrfs = subprocess.check_output(["findmnt", "--noheadings", "--output=FSTYPE", "/"]).strip() == b"btrfs"


def slow_exe(argv: list[str], **kwargs) -> None:
    """Run a command with tests/slow-exit.so

    Use this for test commands under fatrace, not for setup.
    """
    env = os.environ.copy()
    env["LD_PRELOAD"] = str(TESTDIR / "slow-exit.so")
    exe(argv, env=env, **kwargs)


def which(cmd: str) -> str:
    w = shutil.which(cmd)
    assert w
    return str(Path(w).resolve())


def retry_unmount(path: str) -> None:
    for _ in range(5):
        try:
            subprocess.call(["umount", path])
            break
        except subprocess.CalledProcessError as e:
            print(f"Retrying umount {path}: {e}")
            time.sleep(0.5)
    else:
        raise RuntimeError(f"Failed to unmount {path}")

class FatraceRunner():
    """Run text and json fatrace runners in parallel. args must include `--json`."""
    def __init__(self, *args: str) -> None:
        assert "--json" in args
        # create our own private log dir
        self.log_dir: tempfile.TemporaryDirectory[str] = tempfile.TemporaryDirectory()
        self.text_output_file: str = os.path.join(self.log_dir.name, "fatrace.log.txt")
        self.json_output_file: str = os.path.join(self.log_dir.name, "fatrace.log.json")
        self.finished: bool = False
        fatrace_bin = "fatrace" if os.getenv("FATRACE_INSTALLED_TEST") else str(ROOTDIR / "fatrace")
        # start processes
        self.text_process: subprocess.Popen[bytes] = subprocess.Popen(
            [fatrace_bin, "-o", str(self.text_output_file)] +
             [x for x in args if x!="--json"])
        self.json_process: subprocess.Popen[bytes] = subprocess.Popen(
            [fatrace_bin, "-o", str(self.json_output_file), *args])
        # wait until both fatrace starts
        while not (os.path.exists(self.text_output_file) and
                   os.path.exists(self.json_output_file)):
            time.sleep(0.1)
    def finish(self) -> None:
        assert not self.finished
        # fallback timeout; tests should use -s
        self.text_process.wait(timeout=10)
        self.json_process.wait(timeout=10)
        # read log data
        with open(self.text_output_file,
                  'rb', # Binary, so we can handle invalid utf-8 etc.
                  ) as f:
            text_log_contentb: bytes = f.read()
        with open(self.json_output_file, 'r',
                  encoding='utf-8') as f:
            self.json_log_content: str = f.read()
        # process log data
        self.text_log_linesb: list[bytes] = [
            lineb
            for lineb in text_log_contentb.strip().split(b'\n')
            if lineb]
        self.text_log_parsedb: list[tuple[bytes, Event]] = [
            (lineb, parse_fatrace_text_line(lineb))
            for lineb in self.text_log_linesb
            if lineb]
        self.json_log_objs = [
            json.loads(line)
            for line in self.json_log_content.strip().split('\n')
            if line]
        # remove temporary directory
        self.log_dir.cleanup()
        self.finished = True
    def assert_log(self, pred: Pred, regex: Union[str, bytes], present = True) -> None:
        assert self.finished
        regexb = regex.encode('latin-1') if isinstance(regex, str) else regex
        # determine whether text log matches
        text_matches = False
        for lineb in self.text_log_linesb:
            if re.search(regexb, lineb):
                text_matches = True
        # assert that text log matches / does not match
        assert text_matches == present, (
            f"{"No" if present else "At least one"} text entry matched regex\n"
            f"Regex: {repr(regex)}\n"
            "---- Log content ----\n"
            f"{'\n'.join(map(repr, self.text_log_linesb))}\n"
            "-----------------")
        # determine whether json log matches
        json_matches = False
        for obj in self.json_log_objs:
            try:
                if pred(obj):
                    json_matches = True
            except KeyError:
                # Ignore entries that do not match the expected structure
                pass
        # assert that json log matches / does not match
        assert json_matches == present, (
            f"{"No" if present else "At least one"} JSON entry matched lambda\n"
            "---- Log content ----\n"
            f"{self.json_log_content}\n"
            "-----------------")
        # For each text mode output line, assert that the regex matches it iff
        # the predicate matches it after parsing
        for (lineb, obj) in self.text_log_parsedb:
            regex_matches = bool(re.search(regexb, lineb))
            pred_matches = False
            try:
                if pred(obj):
                    pred_matches = True
            except KeyError:
                # Entries that do not match the expected structure, don't match.
                pass
            assert regex_matches == pred_matches, (
                f"Text/JSON conditions mismatch.\n"
                f"Line: {repr(lineb)}\n"
                f"Regex: {repr(regexb)}\n"
                f"Regex matches: {regex_matches}\n"
                f"Line parses to: {obj}\n"
                f"Predicate matches: {pred_matches}\n"
            )
    def assert_not_log(self, pred: Pred, regex: str) -> None:
        self.assert_log(pred, regex, False)

def parse_fatrace_text_line(line: bytes) -> Event:
    """Given a line from fatrace text mode output, return the deserialized expected output for that event in JSON mode."""
    result: Event = {}
    remaining = line.strip()
    timestamp_match = re.match(rb'^(\d{2}:\d{2}:\d{2}\.\d{6}|\d+\.\d{6})\s+', remaining)
    if timestamp_match:
        result['timestamp'] = timestamp_match.group(1).decode()
        remaining = remaining[timestamp_match.end():]
    proc_match = re.match(rb'([^(]+)\((\d+)\)(?:\s+\[(\d+):(\d+)\])?\s*:\s+', remaining)
    if not proc_match:
        raise ValueError(f"Could not parse process info from: {repr(line)}")
    procname = proc_match.group(1).decode()
    if procname != 'unknown':
        result['comm'] = procname
    result['pid'] = int(proc_match.group(2))
    if proc_match.group(3) is not None:
        result['uid'] = int(proc_match.group(3))
        result['gid'] = int(proc_match.group(4))
    remaining = remaining[proc_match.end():]
    types_match = re.match(rb'([RCWO+D<>]+)\s+', remaining)
    if types_match:
        result['types'] = types_match.group(1).decode()
        remaining = remaining[types_match.end():]
    device_match = re.match(rb'device (\d+):(\d+) inode (\d+)', remaining)
    if device_match:
        result['device'] = {'major': int(device_match.group(1)), 'minor': int(device_match.group(2))}
        result['inode'] = int(device_match.group(3))
        remaining = remaining[device_match.end():].lstrip()
    parts = re.split(rb'(\s+exe=|\s+,\s*parents)', remaining)
    if parts and parts[0].strip() and parts[0].strip() != '(deleted)':
        path = parts[0].strip()
        path_is_nonfunny_utf8 = True
        try:
            path.decode()
        except UnicodeDecodeError:
            path_is_nonfunny_utf8 = False
        if set(path).intersection(set([*range(0x20), 0x22, 0x5c, 0x7f])):
            path_is_nonfunny_utf8 = False
        if path_is_nonfunny_utf8:
            result['path'] = path.decode()
        else:
            result['path_raw'] = [*path]
    exe_match = re.search(rb'\s+exe=([^\s,]+)', remaining)
    if exe_match:
        result['exe'] = exe_match.group(1).decode()
    parents_match = re.search(rb',\s*parents=(.+)$', remaining)
    if parents_match:
        parents: list[Parent] = []
        for parent_match in re.findall(rb'\(([^)]+)\)', parents_match.group(1)):
            parent: Parent = {}
            pid_match = re.search(rb'pid=(\d+)', parent_match)
            if pid_match:
                parent['pid'] = int(pid_match.group(1))
            comm_match = re.search(rb'comm=([^\s]+)', parent_match)
            if comm_match:
                parent['comm'] = comm_match.group(1).decode()
            exe_match = re.search(rb'exe=([^\s]+)', parent_match)
            if exe_match:
                parent['exe'] = exe_match.group(1).decode()
            if parent:
                parents.append(parent)
        if parents:
            result['parents'] = parents
    result["parsed_from_text_log"] = True
    return result

class FatraceTests(unittest.TestCase):
    def setUp(self):
        self.tmp_dir = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp_dir.cleanup)
        self.tmp_path = Path(self.tmp_dir.name)

        # isolated mount, so that --current-mount is shielded from other actions in the OS,
        # in particular writing our log file
        exe(["mount", "-t", "tmpfs", "-o", "size=250M", "tmpfs", str(self.tmp_path)])
        self.addCleanup(retry_unmount, str(self.tmp_path))
        # change away from mount to avoid EBUSY
        self.addCleanup(os.chdir, TESTDIR)

        os.chdir(self.tmp_path)

    def test_currentmount(self):
        f = FatraceRunner("--current-mount", "-s", "2", "--json")

        # Create/write/remove a file
        test_file = self.tmp_path / "test.txt"
        slow_exe(["touch", str(test_file)])
        slow_exe(["bash", "-c", f"echo hello > '{test_file}'"])
        slow_exe(["head", str(test_file)], stdout=subprocess.DEVNULL)
        slow_exe(["rm", str(test_file)])

        # moving within same directory
        slow_exe(["touch", str(test_file)])
        test_file_2 = self.tmp_path / "test.txt.2"
        slow_exe(["mv", str(test_file), str(test_file_2)])

        # Create destination directory and move file there
        dest_dir = self.tmp_path / "dest"
        slow_exe(["mkdir", str(dest_dir)])
        dest_file = dest_dir / "test.txt.2"
        slow_exe(["mv", str(test_file_2), str(dest_file)])
        slow_exe(["rm", str(dest_file)])
        slow_exe(["rmdir", str(dest_dir)])

        # Test robustness against ELOOP
        link_file = self.tmp_path / "link"
        slow_exe(["ln", "-s", "nothing", str(link_file)])
        slow_exe(["rm", str(link_file)])

        f.finish()

        cwd = str(self.tmp_path)
        cwd_re = re.escape(cwd)
        test_file_str = str(test_file)

        # file creation
        f.assert_log(lambda e: e["comm"] == "touch" and e["path"] == test_file_str and "O" in e["types"],
                     rf"^touch.*\sC?W?O\s+{re.escape(test_file_str)}")
        f.assert_log(lambda e: e["comm"] == "touch" and e["path"] == test_file_str and "W" in e["types"],
                     rf"^touch.*\sC?WO?\s+{re.escape(test_file_str)}")
        f.assert_log(lambda e: e["comm"] == "bash" and e["path"] == test_file_str and "W" in e["types"],
                     rf"^bash.*\sC?WO?\s+{re.escape(test_file_str)}")

        # file reading
        f.assert_log(lambda e: e["comm"] == "head" and e["path"] == test_file_str and "R" in e["types"],
                     rf"^head.*\sRC?O?\s+{re.escape(test_file_str)}")

        # file deletion
        f.assert_log(lambda e: e["comm"] == "rm" and e["path"] == cwd and e["types"] == "D",
                     rf"^rm\(.*:\s+D\s+{cwd_re}$")

        # directory creation
        f.assert_log(lambda e: e["comm"] == "touch" and e["path"] == cwd and e["types"] == "+",
                     rf"^touch.*:\s+\+\s+{cwd_re}$")
        f.assert_log(lambda e: e["comm"] == "mkdir" and e["path"] == cwd and e["types"] == "+",
                     rf"^mkdir.*:\s+\+\s+{cwd_re}$")

        # file renaming (can be one or two events)
        f.assert_log(lambda e: e["comm"] == "mv" and e["path"] == cwd and "<" in e["types"],
                     rf"^mv.*:\s+<>?\s+{cwd_re}$")
        f.assert_log(lambda e: e["comm"] == "mv" and e["path"] == cwd and ">" in e["types"],
                     rf"^mv.*:\s+<?>\s+{cwd_re}$")

        # file moving between directories
        f.assert_log(lambda e: e["comm"] == "mv" and e["path"] == cwd and e["types"] == "<",
                     rf"^mv.*:\s+<\s+{cwd_re}$")
        f.assert_log(lambda e: e["comm"] == "mv" and e["path"] == str(dest_dir) and e["types"] == ">",
                     rf"^mv.*:\s+>\s+{re.escape(str(dest_dir))}$")

        # ELOOP symlink operations
        f.assert_log(lambda e: e["comm"] == "ln" and e["path"] == cwd and e["types"] == "+",
                     rf"^ln.*:\s+\+\s+{cwd_re}$")
        f.assert_log(lambda e: e["comm"] == "rm" and e["path"] == cwd and e["types"] == "D",
                     rf"^rm\(.*:\s+D\s+{cwd_re}$")

    def test_command(self):
        f = FatraceRunner("--current-mount", "--command", "touch", "-s", "2", "--json")

        # Create files with different programs
        slow_exe(["touch", str(self.tmp_path / "includeme")])
        slow_exe(["dd", "if=/dev/zero", f"of={self.tmp_path}/notme", "bs=1", "count=1", "status=none"])

        f.finish()

        # Check log: should find touch command, but not dd nor the file it created
        includeme_path = str(self.tmp_path / "includeme")
        f.assert_log(lambda e: e["path"] == includeme_path,
                     r"^touch.*includeme$")
        f.assert_not_log(lambda e: "notme" in e["path"],
                         r"notme")
        f.assert_not_log(lambda e: e["comm"]=="dd",
                         r"^dd")

    def test_command_long_name(self):
        # command name that exceeds TASK_COMM_LEN (16 chars)
        long_cmd = self.tmp_path / "VeryLongTouchCommand"
        # Use our own simple-touch binary instead of /usr/bin/touch, to work with both
        # GNU coreutils (standalone binaries) and Rust coreutils (multi-call binary
        # that determines the utility based on argv[0])
        simple_touch = TESTDIR / "simple-touch"
        exe(["cp", str(simple_touch), str(long_cmd)])

        f = FatraceRunner("--current-mount", "--command", "VeryLongTouchCommand", "-s", "2", "--json")
        slow_exe([str(long_cmd), str(self.tmp_path / "hello.txt")])

        f.finish()

        # Should find the truncated command name (first 15 chars per TASK_COMM_LEN-1)
        f.assert_log(lambda e: e["comm"]=="VeryLongTouchCo" and "W" in e["types"] and e["path"]==f"{str(self.tmp_path)}/hello.txt",
                     rf"^VeryLongTouchCo\(.*C?WO?\s+{str(self.tmp_path)}/hello\.txt$")

    def test_btrfs(self):
        if not shutil.which("mkfs.btrfs"):
            self.skipTest("mkfs.btrfs not installed")

        # Create btrfs filesystem
        image_file = self.tmp_path / "btrfs.img"
        mount_dir = self.tmp_path / "mount"

        exe(["dd", "if=/dev/zero", f"of={image_file}", "bs=1M", "count=200", "status=none"])
        exe(["mkfs.btrfs", "--quiet", str(image_file)])
        mount_dir.mkdir()
        exe(["mount", "-o", "loop", str(image_file), str(mount_dir)])
        self.addCleanup(retry_unmount, str(mount_dir))
        # Change away from mount point
        self.addCleanup(os.chdir, self.tmp_path)

        # Create subvolume
        os.chdir(mount_dir)
        exe(["btrfs", "subvolume", "create", str(mount_dir / "subv1")])

        # create initial file
        slow_exe(["bash", "-c", "echo hello > world.txt"])

        f = FatraceRunner("--current-mount", "-s", "2", "--json")

        # Read existing file
        slow_exe(["head", str(mount_dir / "world.txt")], stdout=subprocess.DEVNULL)

        # Standard file operations
        test_file = mount_dir / "test.txt"
        slow_exe(["touch", str(test_file)])
        slow_exe(["bash", "-c", f"echo hello > '{test_file}'"])
        slow_exe(["rm", str(test_file)])

        # Move a file within the same directory
        slow_exe(["touch", str(test_file)])
        test_file_2 = mount_dir / "test.txt.2"
        slow_exe(["mv", str(test_file), str(test_file_2)])
        dest_dir = mount_dir / "dest"
        slow_exe(["mkdir", str(dest_dir)])
        dest_file = dest_dir / "test.txt.2"
        slow_exe(["mv", str(test_file_2), str(dest_file)])
        slow_exe(["rm", str(dest_file)])
        slow_exe(["rmdir", str(dest_dir)])

        # Create file on subvolume
        subvol_file = mount_dir / "subv1" / "sub.txt"
        slow_exe(["touch", str(subvol_file)])

        f.finish()

        mount_str = str(mount_dir)

        # world.txt access
        f.assert_log(lambda e: "R" in e["types"] and e["path"]==str(mount_dir / 'world.txt'),
                     rf"RC?O?\s+{re.escape(str(mount_dir / 'world.txt'))}$")

        # file operations on main filesystem
        test_file_str = str(test_file)
        f.assert_log(lambda e: e["comm"]=="touch" and "O" in e["types"] and e["path"]==test_file_str,
                     rf"^touch.*\sC?W?O\s+{re.escape(test_file_str)}")
        f.assert_log(lambda e: e["comm"]=="touch" and "W" in e["types"] and e["path"]==test_file_str,
                     rf"^touch.*\sC?WO?\s+{re.escape(test_file_str)}")
        f.assert_log(lambda e: e["comm"]=="bash" and "W" in e["types"] and e["path"]==test_file_str,
                     rf"^bash.*\sC?WO?\s+{re.escape(test_file_str)}")
        f.assert_log(lambda e: e["comm"]=="rm" and e["types"] in ["", "D"] and e["path"]==mount_str,
                     rf"^rm\(.*\sD?\s+{re.escape(mount_str)}$")

        # directory creation
        f.assert_log(lambda e: e["comm"]=="touch" and e["types"] == "+" and e["path"]==mount_str,
                     rf"^touch.*:\s+\+\s+{re.escape(mount_str)}$")
        f.assert_log(lambda e: e["comm"]=="mkdir" and e["types"] == "+" and e["path"]==mount_str,
                     rf"^mkdir.*:\s+\+\s+{re.escape(mount_str)}$")

        # file renaming (can be one or two events)
        f.assert_log(lambda e: e["comm"]=="mv" and "<" in e["types"] and e["path"]==mount_str,
                     rf"^mv.*:\s+<>?\s+{re.escape(mount_str)}$")
        f.assert_log(lambda e: e["comm"]=="mv" and ">" in e["types"] and e["path"]==mount_str,
                     rf"^mv.*:\s+<?>\s+{re.escape(mount_str)}$")

        # file moving
        f.assert_log(lambda e: e["comm"]=="mv" and e["types"]=="<" and e["path"]==mount_str,
                     rf"^mv.*:\s+<\s+{re.escape(mount_str)}$")
        f.assert_log(lambda e: e["comm"]=="mv" and e["types"]==">" and e["path"]==str(dest_dir),
                     rf"^mv.*:\s+>\s+{re.escape(str(dest_dir))}$")

        # subvolume file creation
        f.assert_log(lambda e: e["comm"]=="touch" and "O" in e["types"] and e["path"]==str(subvol_file),
                     rf"^touch.*\sC?W?O\s+{re.escape(str(subvol_file))}")

    def test_exe_parents(self):
        f = FatraceRunner("--current-mount", "-s", "2", "--parents", "--exe", "--json")

        # Create complex parent chain: touch → bash → python3 → test
        test_file = self.tmp_path / "file.tmp"
        bash_pid_file = self.tmp_path / "bash.pid"
        python_pid_file = self.tmp_path / "python.pid"

        python_script = f'''
import os, subprocess
subprocess.run(["bash", "-c", "touch {test_file}; echo $$ > {bash_pid_file}"])
with open("{python_pid_file}", "w") as f: f.write(f"{{os.getpid()}}\\n")
'''
        slow_exe([sys.executable, "-c", python_script])

        f.finish()

        # Read process information
        bash_pid = int(bash_pid_file.read_text().strip())
        python_pid = int(python_pid_file.read_text().strip())
        test_pid = os.getpid()

        # Get executable paths
        touch_exe = which("touch")
        bash_exe = which("bash")
        python_exe = which("python3")
        test_exe = Path("/proc/self/exe").resolve()
        init_comm = Path("/proc/1/comm").read_text().strip()
        init_exe = Path("/proc/1/exe").resolve()

        # Check log for parent chain
        f.assert_log(lambda e: (
            e["comm"] == "touch" and
            e["path"] == str(test_file) and
            e["exe"] == str(touch_exe) and
            len(e["parents"]) >= 4 and
            e["parents"][0] == {"pid": bash_pid, "comm": "bash", "exe": str(bash_exe)} and
            e["parents"][1] == {"pid": python_pid, "comm": "python3", "exe": str(python_exe)} and
            e["parents"][2] == {"pid": test_pid, "comm": "python3", "exe": str(python_exe)} and
            e["parents"][-1] == {"pid": 1, "comm": init_comm, "exe": str(init_exe)}
        ),
            rf"^touch.* {re.escape(str(test_file))} "
            rf"exe={re.escape(str(touch_exe))}, "
            rf"parents=\(pid={bash_pid} comm=bash exe={re.escape(str(bash_exe))}\),"
            rf"\(pid={python_pid} comm=python3 exe={re.escape(str(python_exe))}\),"
            rf"\(pid={test_pid} .* exe={re.escape(str(test_exe))}\),.*"
            rf"\(pid=1 comm={init_comm} exe={re.escape(str(init_exe))}\)")

    def test_user(self):
        nobody_user = pwd.getpwnam('nobody')
        nobody_uid = nobody_user.pw_uid
        nobody_gid = nobody_user.pw_gid

        test_file = self.tmp_path / "testfile.txt"
        test_file.write_text("test content")

        # Test user tracking functionality
        f = FatraceRunner("--current-mount", "--user", "-s", "4", "--json")

        def slow_exe_nobody(argv: list[str], **kwargs) -> None:
            exe(["runuser", "-u", "nobody",
                 "env", "LD_PRELOAD=" + str(TESTDIR / "slow-exit.so")] + argv,
                **kwargs)

        # read test file as root
        slow_exe(["head", str(test_file)], stdout=subprocess.DEVNULL)
        # read test file as nobody
        slow_exe_nobody(["tail", str(test_file)], stdout=subprocess.DEVNULL)

        # Create/remove a file as root
        test_file_root = self.tmp_path / "testroot.txt"
        slow_exe(["touch", str(test_file_root)])
        slow_exe(["rm", str(test_file_root)])

        # Create a world-writable directory for user operations
        user_tmp = self.tmp_path / "user_tmp"
        user_tmp.mkdir()
        user_tmp.chmod(0o1777)

        # Create/remove a file as user 'nobody'
        test_file_user = user_tmp / "testnobody.txt"
        slow_exe_nobody(["touch", str(test_file_user)])
        slow_exe_nobody(["rm", str(test_file_user)])

        f.finish()

        test_file_str = str(test_file)
        test_file_root_str = str(test_file_root)
        test_file_user_str = str(test_file_user)

        # Reading the test file as root [0:0]
        f.assert_log(lambda e: (
            e["comm"] == "head" and
            e["uid"] == 0 and
            e["gid"] == 0 and
            "R" in e["types"] and
            e["path"] == test_file_str
        ),
                     rf"^head.*\[0:0\].*RC?O?\s+{re.escape(test_file_str)}$")

        # Reading the test file as user nobody [uid:gid]
        f.assert_log(lambda e: (
            e["comm"] == "tail" and
            e["uid"] == nobody_uid and
            e["gid"] == nobody_gid and
            "R" in e["types"] and
            e["path"] == test_file_str
        ),
                     rf"^tail.*\[{nobody_uid}:{nobody_gid}\].*RC?O?\s+{re.escape(test_file_str)}$")

        # File creation as root [0:0]
        f.assert_log(lambda e: (
            e["comm"] == "touch" and
            e["uid"] == 0 and
            e["gid"] == 0 and
            "O" in e["types"] and
            e["path"] == test_file_root_str
        ),
                     rf"^touch.*\[0:0\].*C?W?O\s+{re.escape(test_file_root_str)}$")

        # File creation as user nobody [uid:gid]
        f.assert_log(lambda e: (
            e["comm"] == "touch" and
            e["uid"] == nobody_uid and
            e["gid"] == nobody_gid and
            "O" in e["types"] and
            e["path"] == test_file_user_str
        ),
                     rf"^touch.*\[{nobody_uid}:{nobody_gid}\].*C?W?O\s+{re.escape(test_file_user_str)}$")

    def test_json(self):
        """JSON-specific features like path_raw, UTF-8 handling, device/inode, etc."""
        f = FatraceRunner("--current-mount", "--user", "-s", "10", "--json")

        # Test 1: Basic path tracking
        good_file = self.tmp_path / "1-good.tmp"
        slow_exe(["touch", str(good_file)])

        # Test 2: path_raw for non-UTF8 paths
        bad_file = self.tmp_path / f"2-bad-{chr(1)}.tmp"
        slow_exe(["touch", str(bad_file)])

        # Test 3: pid tracking
        pid_file = self.tmp_path / "3-pid"
        slow_exe(["bash", "-c", f"echo $$ > '{pid_file}'"])

        # Test 4: device and inode tracking
        device_file = self.tmp_path / "4-good.tmp"
        slow_exe(["touch", str(device_file)])

        # Test 5: UTF-8 test cases - keep as raw bytes for bad cases
        # (expected_result, filename_bytes, description)
        utf8_test_cases = [
            ("bad", b"\x05-tmp", "0x05"),
            ("bad", b"\x1f-tmp", "0x1f"),
            ("good", b"\x20-tmp", "0x20 space"),
            ("good", b"\x21-tmp", "0x21 !"),
            ("bad", b"\x22-tmp", "0x22 \""),
            ("good", b"\x23-tmp", "0x23 #"),
            ("good", b"\x5b-tmp", "0x5b ["),
            ("bad", b"\x5c-tmp", "0x5c \\"),
            ("good", b"\x5d-tmp", "0x5d ]"),
            ("good", b"\x7e-tmp", "0x7e ~"),
            ("bad", b"\x7f-tmp", "0x7f"),
            # 2-char UTF-8
            ("good", "\u0080-tmp".encode(), "U+0080"),
            ("good", "\u00c5-tmp".encode(), "U+00c5 Å"),
            ("bad", b"\xc3-tmp", "incomplete UTF-8"),
            ("good", "\u07ff-tmp".encode(), "U+07ff ߿"),
            # 3-char UTF-8
            ("good", "\u0800-tmp".encode(), "U+0800 ࠀ"),
            ("good", "\u0bf5-tmp".encode(), "U+0bf5 ௵"),
            ("bad", b"\xe0\xaf-tmp", "incomplete UTF-8"),
            ("good", "\ud7ff-tmp".encode(), "U+d7ff"),
            ("bad", b"\xed\xa0\x80-tmp", "surrogate U+d800"),
            ("good", "\ue000-tmp".encode(), "U+e000"),
            ("good", "\uffff-tmp".encode(), "U+ffff"),
            # 4-char UTF-8
            ("good", "\U00010000-tmp".encode(), "U+10000 𐀀"),
            ("good", "\U0001f005-tmp".encode(), "U+1f005 🀅"),
            ("bad", b"\xf0\x9f\x80-tmp", "incomplete UTF-8"),
            ("good", "\U0010ffff-tmp".encode(), "U+10ffff"),
            # continuation bytes
            ("bad", b"\x80-tmp", "0x80"),
            ("bad", b"\xbf-tmp", "0xbf"),
        ]

        created_utf8_files = []
        for expected, filename_bytes, description in utf8_test_cases:
            full_filename_bytes = b"utf8-" + expected.encode('ascii') + b"-" + filename_bytes

            # Use printf to create the exact filename with byte sequences
            printf_arg = ''.join(f'\\{b:03o}' for b in full_filename_bytes)
            slow_exe(["bash", "-c", f"touch \"$(printf '{printf_arg}')\""])

            created_utf8_files.append((expected, full_filename_bytes, description))

        f.finish()

        # Test 1: Basic path tracking
        f.assert_log(lambda e: e["comm"] == "touch" and e["path"] == str(good_file),
                     rf"^touch\([0-9]*\).* {re.escape(str(good_file))}$")

        # Test 2: path_raw for non-UTF8 paths
        # For files with invalid UTF-8, should have path_raw instead of path
        f.assert_log(lambda e: e["comm"] == "touch" and
                     e["path_raw"] == list(str(bad_file).encode('utf-8')) and
                     "path" not in e,
                     rf"^touch\([0-9]*\).* {re.escape(str(bad_file))}$")

        # Test 3: pid tracking
        recorded_pid = int(pid_file.read_text().strip())
        f.assert_log(lambda e: e["comm"] == "bash" and e["pid"] == recorded_pid and e["path"] == str(pid_file),
                     rf"^bash\({recorded_pid}\).* {re.escape(str(pid_file))}$")

        # Test 4: device and inode tracking
        stat_result = device_file.stat()
        f.assert_log(lambda e:
                     e["comm"] == "touch" and
                     e["path"] == str(device_file) and
                     ("parsed_from_text_log" in e or # Usually the text log has no device or inode
                      (e["device"] == {"major": os.major(stat_result.st_dev),
                                       "minor": os.minor(stat_result.st_dev)} and
                       e["inode"] == stat_result.st_ino)),
                     rf"^touch\([0-9]*\).* {re.escape(str(device_file))}$")

        # Test 5: UTF-8 validation - test both good and bad cases properly
        for expected, filename_bytes, description in created_utf8_files:
            # Calculate the full path bytes
            full_path_bytes = str(self.tmp_path).encode('utf-8') + b"/" + filename_bytes

            if expected == "good":
                # Good UTF-8: should be decodable and have "path" field, should NOT have "path_raw"
                file_path_str = full_path_bytes.decode('utf-8')
                # We're abusing latin-1 to represent bytes
                file_path_strbytes = full_path_bytes.decode('latin-1')
                f.assert_log(lambda e:
                             e["comm"] == "touch" and
                             "comm_raw" not in e and
                             e["path"] == file_path_str and
                             "path_raw" not in e,
                             rf"^touch\([0-9]*\).* {re.escape(file_path_strbytes)}$")

            else:
                assert expected == "bad"
                # Bad UTF-8: should NOT be decodable and should have "path_raw" field as byte array
                file_bytes_list = list(full_path_bytes)
                file_path_escaped = ''.join(f'\\{b:03o}' for b in full_path_bytes)
                f.assert_log(lambda e:
                             e["comm"] == "touch" and
                             "comm_raw" not in e and
                             e["path_raw"] == file_bytes_list and
                             "path" not in e,
                             rf"^touch\([0-9]*\).* {file_path_escaped}$")

    def test_dir(self):
        yes1 = str(self.tmp_path / "yes-1")
        yes2 = str(self.tmp_path / "yes-2")
        no1 = str(self.tmp_path / "no-1")

        exe(["mkdir", yes1])
        exe(["mkdir", yes2])
        exe(["mkdir", no1])

        fs = [
            FatraceRunner("-s", "3", "-d", yes1, f"--dir={yes2}", "--json"),
            FatraceRunner("-s", "3", "--json", "--", yes1, yes2),
        ]

        slow_exe(["mkdir", f"{yes1}/subA"])
        slow_exe(["mkdir", f"{no1}/subB"])

        slow_exe(["touch", f"{yes1}/yesC"])
        slow_exe(["touch", f"{yes1}/subA/noD"])
        slow_exe(["touch", f"{yes2}/yesE"])
        slow_exe(["touch", f"{no1}/noF"])
        slow_exe(["touch", f"{no1}/subB/noG"])

        slow_exe(["mv", yes1, yes2])
        new_yes1 = str(self.tmp_path / "yes-2" / "yes-1")
        slow_exe(["mv", no1, yes2])
        new_no1 = str(self.tmp_path / "yes-2" / "no-1")

        slow_exe(["touch", f"{new_yes1}/yesH"])
        slow_exe(["touch", f"{new_yes1}/subA/noI"])
        slow_exe(["touch", f"{new_no1}/noJ"])
        slow_exe(["touch", f"{new_no1}/subB/noK"])

        for f in fs:
            f.finish()
            f.assert_log    (lambda e: e["comm"] == "mkdir" and e["types"] == "+" and e["path"] == yes1,
                             rf"^mkdir\([0-9]*\): \+ +{re.escape(yes1)}")
            f.assert_not_log(lambda e: e["comm"] == "mkdir" and e["types"] == "+" and e["path"] == no1,
                             rf"^mkdir\([0-9]*\): \+ +{re.escape(no1)}")
            f.assert_log    (lambda e: e["comm"] == "touch" and "W" in e["types"] and e["path"] == f"{yes1}/yesC",
                             rf"^touch\([0-9]*\): C?WO? +{re.escape(yes1)}/yesC")
            f.assert_not_log(lambda e: e["comm"] == "touch" and "W" in e["types"] and e["path"] == f"{yes1}/subA/noD",
                             rf"^touch\([0-9]*\): C?WO? +{re.escape(yes1)}/subA/noD")
            f.assert_log    (lambda e: e["comm"] == "touch" and "W" in e["types"] and e["path"] == f"{yes2}/yesE",
                             rf"^touch\([0-9]*\): C?WO? +{re.escape(yes2)}/yesE")
            f.assert_not_log(lambda e: e["comm"] == "touch" and "W" in e["types"] and e["path"] == f"{no1}/noF",
                             rf"^touch\([0-9]*\): C?WO? +{re.escape(no1)}/noF")
            f.assert_not_log(lambda e: e["comm"] == "touch" and "W" in e["types"] and e["path"] == f"{no1}/subB/noG",
                             rf"^touch\([0-9]*\): C?WO? +{re.escape(no1)}/subB/noG")
            f.assert_log    (lambda e: e["comm"] == "touch" and "W" in e["types"] and e["path"] == f"{new_yes1}/yesH",
                             rf"^touch\([0-9]*\): C?WO? +{re.escape(new_yes1)}/yesH")
            f.assert_not_log(lambda e: e["comm"] == "touch" and "W" in e["types"] and e["path"] == f"{new_yes1}/subA/noI",
                             rf"^touch\([0-9]*\): C?WO? +{re.escape(new_yes1)}/subA/noI")
            f.assert_not_log(lambda e: e["comm"] == "touch" and "W" in e["types"] and e["path"] == f"{new_no1}/noJ",
                             rf"^touch\([0-9]*\): C?WO? +{re.escape(new_no1)}/noJ")
            f.assert_not_log(lambda e: e["comm"] == "touch" and "W" in e["types"] and e["path"] == f"{new_no1}/subB/noK",
                             rf"^touch\([0-9]*\): C?WO? +{re.escape(new_no1)}/subB/noK")

    @unittest.skipIf("container" in os.environ, "Not supported in container environment")
    @unittest.skipIf(os.path.exists("/sysroot/ostree"), "Test does not work on OSTree")
    @unittest.skipIf(root_is_btrfs, "FANOTIFY does not work on btrfs, https://github.com/martinpitt/fatrace/issues/3")
    def test_all_mounts(self):
        f = FatraceRunner("-s", "2", "--json")

        # read a system file
        slow_exe(["head", "/etc/passwd"], stdout=subprocess.DEVNULL)

        # create file
        test_file = Path("/tmp/fatrace-test.txt")
        slow_exe(["touch", str(test_file)])
        slow_exe(["bash", "-c", f"echo hello > '{test_file}'"])

        # remove file
        slow_exe(["rm", str(test_file)])

        f.finish()

        head_binary = which("head")

        # opening the head binary
        f.assert_log(lambda e: "R" in e["types"] and e["path"] == head_binary,
                     rf"RC?O?\s+{re.escape(head_binary)}$")
        # head accessing /etc/passwd
        f.assert_log(lambda e: "R" in e["types"] and e["path"] == "/etc/passwd",
                     r"RC?O?\s+/etc/passwd$")

        # create a file
        test_file_str = str(test_file)
        f.assert_log(lambda e: e["comm"] == "touch" and "O" in e["types"] and e["path"] == test_file_str,
                     rf"^touch.*C?W?O\s+{re.escape(test_file_str)}")
        f.assert_log(lambda e: e["comm"] == "touch" and "W" in e["types"] and e["path"] == test_file_str,
                     rf"^touch.*C?WO?\s+{re.escape(test_file_str)}")
        f.assert_log(lambda e: e["comm"] == "bash" and "W" in e["types"] and e["path"] == test_file_str,
                     rf"^bash.*C?WO?\s+{re.escape(test_file_str)}")

        # remove file
        f.assert_log(lambda e: e["comm"] == "touch" and e["types"] == "+" and e["path"] == "/tmp",
                     r"^touch.*:\s+\+\s+/tmp$")
        f.assert_log(lambda e: e["comm"] == "rm" and e["types"] == "D" and e["path"] == "/tmp",
                     r"^rm.*:\s+D\s+/tmp$")
