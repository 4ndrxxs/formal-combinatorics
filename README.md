# Formal combinatorics in Lean

This repository collects machine-checked results in combinatorial matrix theory and related discrete mathematics. Proof files and build instructions are in English. The project pins Lean 4.36.0 and mathlib in the Lake manifest.

## Modular Hadamard matrices

An order $n$ is supported at modulus $m$ if there is an $n$-by-$n$ integer sign matrix $H$ with $HH^{T} = nI$ modulo $m$. For positive odd $m$, let $Q_m$n$$ mean that $n$ is a sum of `gcd(n, 4)` squares modulo $m$.

| Result | Formal statement |
| --- | --- |
| Every arithmetic progression through $n$ contains arbitrarily large supported orders if and only if $Q_m$n$$. | [Integer matrix and square-sum statement](Statements/CompositeSquareNormStatement.lean) |
| For every odd modulus with at most two distinct prime factors, $Q_m$n$$ is necessary and sufficient at each sufficiently large $n$. For any fixed odd modulus the same holds when one of $n,n-1,n-2$ is coprime to it. | [Square-norm theorem](Quantum/Hadamard/CompositeSquareNorms.lean) and [three coprimality conditions](Quantum/Hadamard/ThreeCenterConductor.lean) |
| For any odd prime $p$, the sufficiently large supported orders are exactly the even orders and the orders that are squares modulo $p$, including zero. | [Kuperberg's conjecture in integer-matrix form](Statements/KuperbergStatement.lean) |
| Local obstructions and constructive sufficiency at two odd prime powers, with arbitrary exponents. | [Expanded valuation statements](Statements/TwoPrimePowerSpectrumStatement.lean) |

For example, modulo 45, every order congruent to 6 modulo 180 is excluded by its 3-adic valuation. Every sufficiently large order congruent to 18 modulo 180 is supported since $18=3^2+3^2$. The second conclusion has a threshold depending on the modulus. For moduli with more than two prime divisors, the progression theorem alone does not imply pointwise existence.

The prime statement is formulated in [Kuperberg, *Hadamard matrices modulo p and small modular Hadamard matrices*](https://doi.org/10.1002/jcd.21522). Kline's November 2026 preprint proves the prime criterion for odd primes outside the class 1 modulo 8 and supplies design extensions used in this development. [Kline, *Modular Hadamard matrices at large orders*](https://doi.org/10.5281/zenodo.24421216)

## Conference matrices and determinants

Let $C$ be a real symmetric conference matrix of even order $n$, and let $D$ be diagonal with equally many entries of each sign. If $n-1$ is at least 674, the absolute determinant of $C+D$ is at least four fifths of the Ehlich–Wojtas expression $(2n-2)(n-2)^{(n-2)/2}$. The precise matrix hypotheses are in [the determinant theorem](Quantum/Hadamard/DeterminantRatioEstimateConference.lean).

## Reproduce the checks

Install [elan](https://github.com/leanprover/elan) and Git. Run these commands from a checkout.

```sh
lake exe cache get
lake build
lake env lean Statements/CompositeSquareNormStatement.lean
lake env lean Statements/TwoPrimePowerSpectrumStatement.lean
lake env lean Statements/KuperbergStatement.lean
lake env leanchecker -v Quantum.Hadamard.CompositeSquareNorms
lake env leanchecker -v Quantum.Hadamard.DeterminantRatioEstimateConference
```

The standalone statements print their full theorem types and axiom lists. The square-sum endpoints use `propext`, `Classical.choice`, and `Quot.sound`. The source files include earlier constructions and attribute them in the relevant modules. Computational checking establishes the formal statements under the pinned dependencies. Questions of bibliographic priority and journal review are separate.

AI tools assisted with proofs and exposition. Public theorem names, assumptions, and source files are provided so readers can check them independently.
