"""Recompile the research modules and independent statements, then replay their Lean kernels."""

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
        'DeterminantRatioEstimateUnbalanced', 'ConferenceDiagonalAverage', 'ConferenceBalancedMean',
        'ConferencePrincipalDet', 'ConferenceCubicEstimate', 'ConferenceCubicThreshold',
        'ConferenceCubicMatrix', 'Basic', 'Paley', 'ProjectiveQuadraticBalance', 'Conference',
        'PaleySecond', 'TorusFrobeniusPaley', 'ProjectiveSplitSupports', 'ConferenceShiftedLog', 'ConferenceShiftedThreshold',
        'ProjectivePaleyDeterminant',
        'Goethals', 'GoethalsBits', 'ConferenceBitTrace', 'ConferenceBitBound', 'ConferenceBitCompletion',
        'ProjectivePaleyAction', 'ProjectiveQuadraticOrbits', 'ProjectiveFieldModels', 'NearHadamardBorders', 'ProjectiveSupportCorrelations')]
    print(subprocess.check_output([lean, '--version'], cwd=project, env=env, text=True).strip(), flush=True)
    with TemporaryDirectory(prefix='lean-conference-') as temporary:
        tmp = Path(temporary)
        env['LEAN_PATH'] = os.pathsep.join([str(tmp), env['LEAN_PATH']])
        checked = []
        audits = ['verifiedConferenceEstimates', 'verifiedProportionEstimate', 'verifiedBalancedLimit',
                  'verifiedProportionLimit', 'verifiedDiagonalGenerating', 'verifiedBalancedMean',
                  'verifiedAboveLimitAtEveryOrder', 'verifiedAllBalanced110']
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
            expected = audits if rel == Path('Verify.lean') else []
            if rel.name == 'NearHadamardBorders.lean':
                expected = ['Hadamard.NearBorder.' + name for name in
                            ('abs_det_of_border_blocks', 'bordering_rigidity', 'two_circulant_borders')]
            if rel.name == 'ProjectiveSupportCorrelations.lean':
                expected = ['Hadamard.MSXCore.incidence_gram']
            if expected:
                compact = ' '.join(out.stdout.split())
                for theorem in expected:
                    required = f"'{theorem}' depends on axioms: [propext, Classical.choice, Quot.sound]"
                    if required not in compact:
                        raise RuntimeError(f'Unexpected or missing axiom report for {theorem}')
            checked.append(rel)
            print(f'{hashlib.sha256(dest.read_bytes()).hexdigest()}  {rel.as_posix()}', flush=True)
        checker = shutil.which('leanchecker', path=env['PATH'])
        if not checker:
            raise RuntimeError('The Lean kernel checker was not in the Lake environment.')
        for rel in checked:
            module = '.'.join(rel.with_suffix('').parts)
            subprocess.run([checker, '-v', module], cwd=tmp, env=env, check=True)
        print(f'Freshly compiled and kernel-replayed {len(checked)} sources, including all independent statements.')


if __name__ == '__main__':
    main()
