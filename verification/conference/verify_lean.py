"""Recompile the five research modules in a fresh directory and audit their statements."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory


def main():
    folder = Path(__file__).resolve().parent
    root = folder.parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, default=root,
                        help='Lake project providing the pinned Lean and Mathlib installation')
    project = parser.parse_args().project.resolve()
    suffix = '.exe' if os.name == 'nt' else ''
    lake = shutil.which('lake') or str(Path.home() / '.elan' / 'bin' / ('lake' + suffix))
    probe = 'import json, os; print(json.dumps(dict(os.environ)))'
    env = json.loads(subprocess.check_output([lake, 'env', sys.executable, '-c', probe],
                                             cwd=project, text=True, encoding='utf8'))
    lean = shutil.which('lean', path=env['PATH'])
    if not lean:
        raise RuntimeError('The Lean compiler was not in the Lake environment.')
    modules = [Path('Quantum/Hadamard') / (name + '.lean') for name in (
        'DeterminantRatioEstimate', 'DeterminantRatioEstimateMatrix',
        'DeterminantRatioEstimateConference', 'DeterminantRatioEstimateLimit',
        'DeterminantRatioEstimateUnbalanced')]
    print(subprocess.check_output([lean, '--version'], cwd=project, env=env, text=True).strip(), flush=True)
    with TemporaryDirectory(prefix='lean-conference-') as temporary:
        tmp = Path(temporary)
        env['LEAN_PATH'] = os.pathsep.join([str(tmp), env['LEAN_PATH']])
        checked = []
        for rel in [*modules, Path('Statement.lean'), Path('Verify.lean')]:
            src = (root if rel in modules else folder) / rel
            dest = tmp / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, dest)
            out = subprocess.run([lean, '-R', str(tmp), '-o', str(dest.with_suffix('.olean')), str(dest)],
                                 cwd=project, env=env, text=True, encoding='utf8',
                                 stderr=subprocess.STDOUT, stdout=subprocess.PIPE)
            print(out.stdout, end='', flush=True)
            out.check_returncode()
            if 'sorryAx' in out.stdout or 'declaration uses' in out.stdout:
                raise RuntimeError(f'Unproved declaration in {rel}')
            checked.append(rel)
            print(f'{hashlib.sha256(dest.read_bytes()).hexdigest()}  {rel.as_posix()}', flush=True)
        print(f'Freshly compiled {len(checked)} sources, including the independent specification and bridge.')


if __name__ == '__main__':
    main()
