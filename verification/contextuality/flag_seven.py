"""Exhaust the signed-root Fourier permutations fixing the seven-ray seed basis."""
from itertools import permutations
from check import SEED,add

def inspect():
    seed=set(SEED)
    permutations_on_seed=set()
    for pi in permutations(range(7)):
        shifted=[]
        for v in SEED:
            w=(0,*v)
            shifted.append(tuple((w[j]-w[pi[0]])%6 for j in pi[1:]))
        for delta in SEED:
            translated=[add(delta,w) for w in shifted]
            if set(translated)==seed:
                permutations_on_seed.add(tuple(SEED.index(w) for w in translated))
    assert len(permutations_on_seed)==12
    orbits={tuple(sorted({g[i] for g in permutations_on_seed})) for i in range(7)}
    assert sorted(map(len,orbits))==[1,6]
    assert (0,) in orbits
    print('35,280 possibilities for the basis stabilizer; 12 distinct induced permutations; flag orbit lengths 1 and 6')
    return permutations_on_seed

if __name__=='__main__':
    inspect()

