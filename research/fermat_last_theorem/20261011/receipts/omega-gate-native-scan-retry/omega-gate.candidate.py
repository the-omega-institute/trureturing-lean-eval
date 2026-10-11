#!/usr/bin/python3
"""Local admission gate for heavy Lean builds: reserve memory, queue when over budget.

Scope: only trureturing (any worktree whose git common dir is DONOR/.git);
other projects pass straight through.
Used via shims in ~/.local/omega-shims/{lake,lean}: `omega-gate <name> args...`.
Heavy = `lake ... build ...` or `lean ... *.lean`; everything else passes through.

A heavy call is admitted when
    committed + JOB_GB <= BUDGET_GB
    committed = used (active+wired+compressor)
              + sum over running lean-eval lean procs of max(0, EVAL_GB - rss)
              + JOB_GB * (builds admitted in the last RAMP_S=60 seconds)
Builds ramp up after start, so the reservation covers memory not yet touched.
lean-eval itself bypasses the shims (absolute lean path); it is only observed
by a process scan. If no lean/lake runs at all, the call is admitted anyway
(prevents deadlock when non-Lean memory alone exceeds the budget).
Env: OMEGA_GATE_BUDGET_GB=90 OMEGA_GATE_JOB_GB=8 OMEGA_GATE_EVAL_GB=35
     OMEGA_GATE_REQUEST_GB=JOB_GB (candidate reservation; keeps the shared ramp baseline)
     OMEGA_GATE_RAMP_S=60 OMEGA_GATE_EVAL_PAT=--trust=0 OMEGA_GATE_DISABLE=1 (emergency bypass)
Log: ~/Library/Logs/omega-gate.log
"""
import ctypes
import errno
import fcntl, os, re, subprocess, sys, time
from dataclasses import dataclass

HOME = os.path.expanduser('~')
STATE = HOME + '/.local/state/omega-gate'
LOG = HOME + '/Library/Logs/omega-gate.log'
DONOR_GIT = '/Users/macstudio/omega/trureturing/.git'
BUDGET_GB = float(os.environ.get('OMEGA_GATE_BUDGET_GB', 90))
JOB_GB = float(os.environ.get('OMEGA_GATE_JOB_GB', 8))
REQUEST_GB = float(os.environ.get('OMEGA_GATE_REQUEST_GB', JOB_GB))
EVAL_GB = float(os.environ.get('OMEGA_GATE_EVAL_GB', 35))
RAMP_S = float(os.environ.get('OMEGA_GATE_RAMP_S', 60))
EVAL_PAT = os.environ.get('OMEGA_GATE_EVAL_PAT', '--trust=0')  # lean-eval jobs run lean with --trust=0


def log(msg):
    try:
        with open(LOG, 'a') as f:
            f.write('%s pid=%d %s\n' % (time.strftime('%F %T'), os.getpid(), msg))
    except OSError:
        pass


def heavy(name, args):
    if name == 'lake':
        return 'build' in args[:8]
    if name == 'lean':
        return any(a.endswith('.lean') for a in args) and '--server' not in args
    return False


def targets(name, args):
    """Directories this call works on: cwd, lake -d DIR, lean --root=DIR / *.lean parents."""
    out = [os.getcwd()]
    for i, a in enumerate(args):
        if name == 'lake' and a in ('-d', '--dir') and i + 1 < len(args):
            out.append(args[i + 1])
        elif a.startswith('--dir=') or a.startswith('--root='):
            out.append(a.split('=', 1)[1])
        elif a.endswith('.lean'):
            out.append(os.path.dirname(os.path.abspath(a)))
    return out


def in_trureturing(name, args):
    seen = set()
    for d in targets(name, args):
        d = os.path.abspath(d)
        while d and not os.path.isdir(d) and d != '/':
            d = os.path.dirname(d)
        if d in seen:
            continue
        seen.add(d)
        r = subprocess.run(['git', '-C', d, 'rev-parse', '--path-format=absolute', '--git-common-dir'],
                           capture_output=True, text=True)
        if r.returncode == 0 and os.path.realpath(r.stdout.strip()) == os.path.realpath(DONOR_GIT):
            return True
    return False


def used_gb():
    out = subprocess.run(['vm_stat'], capture_output=True, text=True).stdout
    page = int(re.search(r'page size of (\d+)', out).group(1))

    def pages(label):
        m = re.search(label + r':\s+(\d+)', out)
        return int(m.group(1)) if m else 0
    n = pages('Pages active') + pages('Pages wired down') + pages('Pages occupied by compressor')
    return n * page / 2**30


class NativeScanError(RuntimeError):
    pass


class _NativePermission(NativeScanError):
    pass


class _Disappeared(Exception):
    pass


@dataclass(frozen=True)
class _ProcessIdentity:
    pid: int
    start_sec: int
    start_usec: int


@dataclass(frozen=True)
class _KernelProcessRecord:
    identity: _ProcessIdentity
    status: int
    name: str


@dataclass(frozen=True)
class _ProcessName:
    name: str
    kernel_record: _KernelProcessRecord = None


class _ProcBsdInfo(ctypes.Structure):
    _fields_ = [
        ('pbi_flags', ctypes.c_uint32),
        ('pbi_status', ctypes.c_uint32),
        ('pbi_xstatus', ctypes.c_uint32),
        ('pbi_pid', ctypes.c_uint32),
        ('pbi_ppid', ctypes.c_uint32),
        ('pbi_uid', ctypes.c_uint32),
        ('pbi_gid', ctypes.c_uint32),
        ('pbi_ruid', ctypes.c_uint32),
        ('pbi_rgid', ctypes.c_uint32),
        ('pbi_svuid', ctypes.c_uint32),
        ('pbi_svgid', ctypes.c_uint32),
        ('rfu_1', ctypes.c_uint32),
        ('pbi_comm', ctypes.c_char * 16),
        ('pbi_name', ctypes.c_char * 32),
        ('pbi_nfiles', ctypes.c_uint32),
        ('pbi_pgid', ctypes.c_uint32),
        ('pbi_pjobc', ctypes.c_uint32),
        ('e_tdev', ctypes.c_uint32),
        ('e_tpgid', ctypes.c_uint32),
        ('pbi_nice', ctypes.c_int32),
        ('pbi_start_tvsec', ctypes.c_uint64),
        ('pbi_start_tvusec', ctypes.c_uint64),
    ]


class _ProcTaskInfo(ctypes.Structure):
    _fields_ = [
        ('pti_virtual_size', ctypes.c_uint64),
        ('pti_resident_size', ctypes.c_uint64),
        ('pti_total_user', ctypes.c_uint64),
        ('pti_total_system', ctypes.c_uint64),
        ('pti_threads_user', ctypes.c_uint64),
        ('pti_threads_system', ctypes.c_uint64),
        ('pti_policy', ctypes.c_int32),
        ('pti_faults', ctypes.c_int32),
        ('pti_pageins', ctypes.c_int32),
        ('pti_cow_faults', ctypes.c_int32),
        ('pti_messages_sent', ctypes.c_int32),
        ('pti_messages_received', ctypes.c_int32),
        ('pti_syscalls_mach', ctypes.c_int32),
        ('pti_syscalls_unix', ctypes.c_int32),
        ('pti_csw', ctypes.c_int32),
        ('pti_threadnum', ctypes.c_int32),
        ('pti_numrunning', ctypes.c_int32),
        ('pti_priority', ctypes.c_int32),
    ]


class _ProcTaskAllInfo(ctypes.Structure):
    _fields_ = [('pbsd', _ProcBsdInfo), ('ptinfo', _ProcTaskInfo)]


@dataclass(frozen=True)
class _NativeStats:
    listed: int
    observed: int
    disappeared: int


_PROC_ALL_PIDS = 1
_PROC_PIDTASKALLINFO = 2
_PROC_PIDTASKALLINFO_SIZE = ctypes.sizeof(_ProcTaskAllInfo)
_CTL_KERN = 1
_KERN_PROC = 14
_KERN_PROC_PID = 1
_KERN_PROCARGS2 = 49
_KINFO_PROC_SIZE = 648
_KINFO_COMM_OFFSET = 243
_KINFO_COMM_SIZE = 17
_KINFO_START_SEC_OFFSET = 0
_KINFO_START_USEC_OFFSET = 8
_KINFO_STAT_OFFSET = 36
_KINFO_PID_OFFSET = 40
_SZOMB = 5
_VALID_PROC_STATES = frozenset((1, 2, 3, 4, _SZOMB))
_MAX_ARGS_BYTES = 16 * 1024 * 1024
_ABI_SIGNATURE = {
    'bsd_size': 136,
    'task_size': 96,
    'taskall_size': 232,
    'taskall_task_offset': 136,
    'resident_offset': 8,
    'kinfo_size': 648,
    'kinfo_comm_offset': 243,
    'kinfo_start_sec_offset': 0,
    'kinfo_start_usec_offset': 8,
    'kinfo_stat_offset': 36,
    'kinfo_pid_offset': 40,
    'szomb': 5,
}


def _validate_abi(signature=None):
    if sys.platform != 'darwin':
        raise NativeScanError('Darwin native process ABI required')
    actual = {
        'bsd_size': ctypes.sizeof(_ProcBsdInfo),
        'task_size': ctypes.sizeof(_ProcTaskInfo),
        'taskall_size': ctypes.sizeof(_ProcTaskAllInfo),
        'taskall_task_offset': _ProcTaskAllInfo.ptinfo.offset,
        'resident_offset': _ProcTaskInfo.pti_resident_size.offset,
        'kinfo_size': _KINFO_PROC_SIZE,
        'kinfo_comm_offset': _KINFO_COMM_OFFSET,
        'kinfo_start_sec_offset': _KINFO_START_SEC_OFFSET,
        'kinfo_start_usec_offset': _KINFO_START_USEC_OFFSET,
        'kinfo_stat_offset': _KINFO_STAT_OFFSET,
        'kinfo_pid_offset': _KINFO_PID_OFFSET,
        'szomb': _SZOMB,
    }
    expected = _ABI_SIGNATURE if signature is None else signature
    if actual != expected:
        raise NativeScanError('Darwin process ABI mismatch: %r != %r' % (actual, expected))


def _native_library():
    library = ctypes.CDLL(None, use_errno=True)
    library.proc_listpids.argtypes = [ctypes.c_uint32, ctypes.c_uint32, ctypes.c_void_p, ctypes.c_int]
    library.proc_listpids.restype = ctypes.c_int
    library.proc_name.argtypes = [ctypes.c_int, ctypes.c_void_p, ctypes.c_uint32]
    library.proc_name.restype = ctypes.c_int
    library.proc_pidinfo.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_uint64, ctypes.c_void_p, ctypes.c_int]
    library.proc_pidinfo.restype = ctypes.c_int
    library.sysctl.argtypes = [ctypes.POINTER(ctypes.c_int), ctypes.c_uint, ctypes.c_void_p,
                               ctypes.POINTER(ctypes.c_size_t), ctypes.c_void_p, ctypes.c_size_t]
    library.sysctl.restype = ctypes.c_int
    return library


def _native_error(operation, pid=None):
    error = ctypes.get_errno()
    suffix = '' if pid is None else ' pid=%d' % pid
    return NativeScanError('%s%s failed: errno=%d %s' % (operation, suffix, error, os.strerror(error)))


def _list_pids(library):
    capacity = library.proc_listpids(_PROC_ALL_PIDS, 0, None, 0)
    if capacity <= 0:
        raise _native_error('proc_listpids(size)')
    for _ in range(4):
        buffer = (ctypes.c_int * ((capacity + ctypes.sizeof(ctypes.c_int) - 1) // ctypes.sizeof(ctypes.c_int)))()
        returned = library.proc_listpids(_PROC_ALL_PIDS, 0, buffer, ctypes.sizeof(buffer))
        if returned < 0:
            raise _native_error('proc_listpids(data)')
        if returned == 0:
            raise NativeScanError('proc_listpids returned no process records')
        if returned <= ctypes.sizeof(buffer):
            return [int(buffer[i]) for i in range(returned // ctypes.sizeof(ctypes.c_int)) if buffer[i] > 0]
        capacity = returned
    raise NativeScanError('proc_listpids size changed repeatedly')


def _task_info(library, pid):
    info = _ProcTaskAllInfo()
    returned = library.proc_pidinfo(pid, _PROC_PIDTASKALLINFO, 0, ctypes.byref(info), _PROC_PIDTASKALLINFO_SIZE)
    if returned == _PROC_PIDTASKALLINFO_SIZE:
        return info
    error = ctypes.get_errno()
    if error in (errno.ESRCH, errno.ENOENT):
        raise _Disappeared(pid)
    if error == errno.EPERM:
        raise _NativePermission(_native_error('proc_pidinfo(taskallinfo)', pid))
    raise _native_error('proc_pidinfo(taskallinfo)', pid)


def _task_identity(pid, info):
    observed_pid = int(info.pbsd.pbi_pid)
    status = int(info.pbsd.pbi_status)
    start_sec = int(info.pbsd.pbi_start_tvsec)
    start_usec = int(info.pbsd.pbi_start_tvusec)
    if observed_pid != pid or status not in _VALID_PROC_STATES or start_sec <= 0 or start_usec < 0 or start_usec >= 1000000:
        raise NativeScanError('invalid task identity pid=%d observed_pid=%d status=%d start=%d.%06d' %
                              (pid, observed_pid, status, start_sec, start_usec))
    return _ProcessIdentity(pid, start_sec, start_usec)


def _kernel_process_record(library, pid):
    mib = (ctypes.c_int * 4)(_CTL_KERN, _KERN_PROC, _KERN_PROC_PID, pid)
    size = ctypes.c_size_t(_KINFO_PROC_SIZE)
    buffer = ctypes.create_string_buffer(_KINFO_PROC_SIZE)
    if library.sysctl(mib, 4, buffer, ctypes.byref(size), None, 0) != 0:
        error = ctypes.get_errno()
        if error in (errno.ESRCH, errno.ENOENT):
            raise _Disappeared(pid)
        raise _native_error('sysctl(KERN_PROC_PID)', pid)
    required = max(_KINFO_START_USEC_OFFSET + ctypes.sizeof(ctypes.c_uint64),
                   _KINFO_STAT_OFFSET + 1,
                   _KINFO_PID_OFFSET + ctypes.sizeof(ctypes.c_uint32),
                   _KINFO_COMM_OFFSET + _KINFO_COMM_SIZE)
    if size.value < required:
        raise NativeScanError('short KERN_PROC_PID record pid=%d size=%d' % (pid, size.value))
    raw = buffer.raw[:size.value]
    observed_pid = int.from_bytes(raw[_KINFO_PID_OFFSET:_KINFO_PID_OFFSET + 4],
                                  byteorder=sys.byteorder, signed=False)
    start_sec = int.from_bytes(raw[_KINFO_START_SEC_OFFSET:_KINFO_START_SEC_OFFSET + 8],
                               byteorder=sys.byteorder, signed=False)
    start_usec = int.from_bytes(raw[_KINFO_START_USEC_OFFSET:_KINFO_START_USEC_OFFSET + 8],
                                byteorder=sys.byteorder, signed=False)
    status = raw[_KINFO_STAT_OFFSET]
    if observed_pid != pid or status not in _VALID_PROC_STATES or start_sec <= 0 or start_usec >= 1000000:
        raise NativeScanError('invalid KERN_PROC_PID identity pid=%d observed_pid=%d status=%d start=%d.%06d' %
                              (pid, observed_pid, status, start_sec, start_usec))
    raw_name = raw[_KINFO_COMM_OFFSET:_KINFO_COMM_OFFSET + _KINFO_COMM_SIZE]
    name = raw_name.split(b'\0', 1)[0].decode('utf-8', 'replace')
    return _KernelProcessRecord(_ProcessIdentity(pid, start_sec, start_usec), status, name)


def _require_terminal_identity(library, pid, expected=None):
    try:
        first = _kernel_process_record(library, pid)
        second = _kernel_process_record(library, pid)
    except _Disappeared:
        raise NativeScanError('possible process disappeared without terminal identity pid=%d' % pid)
    if first.identity != second.identity or first.status != _SZOMB or second.status != _SZOMB:
        raise NativeScanError('unresolved process lifetime pid=%d' % pid)
    if expected is not None and first.identity != expected:
        raise NativeScanError('unresolved process lifetime pid=%d' % pid)
    return True


def _stable_kernel_live_record(library, pid):
    try:
        first = _kernel_process_record(library, pid)
        second = _kernel_process_record(library, pid)
    except _Disappeared:
        raise NativeScanError('possible process disappeared without stable kernel identity pid=%d' % pid)
    if first.identity != second.identity or first.status != second.status or first.name != second.name:
        raise NativeScanError('unstable KERN_PROC_PID identity pid=%d' % pid)
    return first


def _process_name(library, pid):
    buffer = ctypes.create_string_buffer(256)
    returned = library.proc_name(pid, buffer, ctypes.sizeof(buffer))
    if returned > 0:
        return _ProcessName(buffer.raw[:returned].split(b'\0', 1)[0].decode('utf-8', 'replace'))
    error = ctypes.get_errno()
    if error in (errno.ESRCH, errno.ENOENT):
        raise _Disappeared(pid)
    if error == errno.EPERM:
        return _kernel_process_name(library, pid)
    raise _native_error('proc_name', pid)


def _kernel_process_name(library, pid):
    record = _kernel_process_record(library, pid)
    return _ProcessName(record.name, record)


def _args_contain(library, pid, eval_pat):
    mib = (ctypes.c_int * 3)(_CTL_KERN, _KERN_PROCARGS2, pid)
    size = ctypes.c_size_t(0)
    if library.sysctl(mib, 3, None, ctypes.byref(size), None, 0) != 0:
        error = ctypes.get_errno()
        if error in (errno.ESRCH, errno.ENOENT):
            try:
                _task_info(library, pid)
            except _Disappeared:
                raise
            raise _native_error('sysctl(KERN_PROCARGS2)', pid)
        raise _native_error('sysctl(KERN_PROCARGS2 size)', pid)
    if size.value < ctypes.sizeof(ctypes.c_int) or size.value > _MAX_ARGS_BYTES:
        raise NativeScanError('invalid KERN_PROCARGS2 size pid=%d size=%d' % (pid, size.value))
    buffer = ctypes.create_string_buffer(size.value)
    if library.sysctl(mib, 3, buffer, ctypes.byref(size), None, 0) != 0:
        error = ctypes.get_errno()
        if error in (errno.ESRCH, errno.ENOENT):
            try:
                _task_info(library, pid)
            except _Disappeared:
                raise
            raise _native_error('sysctl(KERN_PROCARGS2 data)', pid)
        raise _native_error('sysctl(KERN_PROCARGS2 data)', pid)
    if size.value < ctypes.sizeof(ctypes.c_int) or size.value > ctypes.sizeof(buffer):
        raise NativeScanError('invalid KERN_PROCARGS2 returned size pid=%d size=%d' % (pid, size.value))
    raw = buffer.raw[:size.value]
    argc = int.from_bytes(raw[:ctypes.sizeof(ctypes.c_int)], byteorder=sys.byteorder, signed=True)
    if argc < 0 or argc > 4096:
        raise NativeScanError('invalid KERN_PROCARGS2 argc pid=%d argc=%d' % (pid, argc))
    offset = ctypes.sizeof(ctypes.c_int)
    executable_end = raw.find(b'\0', offset)
    if executable_end <= offset:
        raise NativeScanError('invalid KERN_PROCARGS2 executable pid=%d' % pid)
    offset = executable_end + 1
    while offset < len(raw) and raw[offset] == 0:
        offset += 1
    parts = []
    for _ in range(argc):
        end = raw.find(b'\0', offset)
        if end < 0:
            raise NativeScanError('unterminated KERN_PROCARGS2 argv pid=%d' % pid)
        parts.append(raw[offset:end])
        offset = end + 1
    return eval_pat.encode() in b' '.join(parts)


def _native_scan(eval_pat=EVAL_PAT, eval_gb=EVAL_GB):
    _validate_abi()
    library = _native_library()
    pids = _list_pids(library)
    reserve, any_build = 0.0, False
    disappeared = 0
    observed = 0
    for pid in pids:
        try:
            initial_info = _task_info(library, pid)
        except _Disappeared:
            if _require_terminal_identity(library, pid):
                disappeared += 1
                continue
        except _NativePermission:
            record = _stable_kernel_live_record(library, pid)
            observed += 1
            if record.status == _SZOMB:
                disappeared += 1
                continue
            name = os.path.basename(record.name)
            if not name:
                raise NativeScanError('native kernel process name unavailable pid=%d' % pid)
            if name == 'lake':
                any_build = True
                continue
            if name == 'lean':
                raise NativeScanError('possible Lean RSS identity inaccessible pid=%d' % pid)
            continue
        observed += 1
        initial_identity = _task_identity(pid, initial_info)
        try:
            name_observation = _process_name(library, pid)
        except _Disappeared:
            if _require_terminal_identity(library, pid, initial_identity):
                disappeared += 1
                continue
        if isinstance(name_observation, str):
            name_observation = _ProcessName(name_observation)
        if name_observation.kernel_record is not None and name_observation.kernel_record.identity != initial_identity:
            raise NativeScanError('process identity changed during name observation pid=%d' % pid)
        name = os.path.basename(name_observation.name)
        if not name:
            raise NativeScanError('native process name unavailable pid=%d' % pid)
        try:
            name_info = _task_info(library, pid)
        except _Disappeared:
            if _require_terminal_identity(library, pid, initial_identity):
                disappeared += 1
                continue
        except _NativePermission:
            record = _stable_kernel_live_record(library, pid)
            if record.identity != initial_identity or os.path.basename(record.name) != name:
                raise NativeScanError('process identity changed during permission fallback pid=%d' % pid)
            if record.status == _SZOMB:
                disappeared += 1
                continue
            if name == 'lake':
                any_build = True
                continue
            if name == 'lean':
                raise NativeScanError('possible Lean RSS identity inaccessible pid=%d' % pid)
            continue
        if _task_identity(pid, name_info) != initial_identity:
            raise NativeScanError('process identity changed after name observation pid=%d' % pid)
        if name == 'lean':
            try:
                is_eval = _args_contain(library, pid, eval_pat)
            except _Disappeared:
                if _require_terminal_identity(library, pid, initial_identity):
                    disappeared += 1
                    continue
            try:
                final_info = _task_info(library, pid)
            except _Disappeared:
                if _require_terminal_identity(library, pid, initial_identity):
                    disappeared += 1
                    continue
            if _task_identity(pid, final_info) != initial_identity:
                raise NativeScanError('process identity changed after argv observation pid=%d' % pid)
            any_build = True
            if is_eval:
                reserve += max(0.0, eval_gb - final_info.ptinfo.pti_resident_size / 2**30)
        elif name == 'lake':
            any_build = True
    return reserve, any_build, _NativeStats(len(pids), observed, disappeared)


def scan():
    """(eval_reserve_gb, lean_or_lake_running) from one native read-only pass."""
    reserve, any_build, _ = _native_scan()
    return reserve, any_build


def recent_admits(path, now):
    try:
        ts = [float(x) for x in open(path).read().split()]
    except (OSError, ValueError):
        ts = []
    return [t for t in ts if now - t < RAMP_S]


def main():
    name, args = sys.argv[1], sys.argv[2:]
    real = os.environ.get('OMEGA_GATE_REAL_DIR', HOME + '/.elan/bin') + '/' + name
    if os.environ.get('OMEGA_GATE_DISABLE') == '1' or os.environ.get('OMEGA_GATE_HELD') == '1' \
            or not heavy(name, args) or not in_trureturing(name, args):
        os.execv(real, [name] + args)

    os.makedirs(STATE, exist_ok=True)
    adm = os.open(STATE + '/admission', os.O_RDWR | os.O_CREAT, 0o644)
    ramp_file = STATE + '/recent'
    t0, waited = time.time(), False
    while True:
        fcntl.flock(adm, fcntl.LOCK_EX)  # one candidate at a time; released on exec/close
        now = time.time()
        used = used_gb()
        try:
            eval_res, any_build = scan()
        except NativeScanError as error:
            # An incomplete process snapshot cannot admit a build. Release the
            # admission mutex and take a fresh snapshot after the normal wait.
            fcntl.flock(adm, fcntl.LOCK_UN)
            if not waited:
                waited = True
                why = 'native process observation incomplete: %s' % error
                sys.stderr.write('omega-gate: waiting (%s)\n' % why)
                log('wait %s: %s cwd=%s' % (name, why, os.getcwd()))
            time.sleep(5)
            continue
        ts = recent_admits(ramp_file, now)
        committed = used + eval_res + JOB_GB * len(ts)
        if committed + REQUEST_GB <= BUDGET_GB or not any_build:
            ts.append(now)
            with open(ramp_file, 'w') as f:
                f.write(' '.join('%.0f' % t for t in ts))
            log('admit %s waited=%.0fs used=%.1fG eval_res=%.1fG ramp=%d committed=%.1fG cwd=%s'
                % (name, now - t0, used, eval_res, len(ts) - 1, committed, os.getcwd()))
            os.environ['OMEGA_GATE_HELD'] = '1'
            os.execv(real, [name] + args)
        why = 'committed %.1fG (used %.1f + eval %.1f + ramp %d*%.0f) + %.0f > budget %.0fG' % (
            committed, used, eval_res, len(ts), JOB_GB, REQUEST_GB, BUDGET_GB)
        fcntl.flock(adm, fcntl.LOCK_UN)
        if not waited:
            waited = True
            sys.stderr.write('omega-gate: waiting (%s)\n' % why)
            log('wait %s: %s cwd=%s' % (name, why, os.getcwd()))
        time.sleep(5)


if __name__ == '__main__':
    main()
