# Formal combinatorics in Lean

This repository collects machine-checked results in combinatorial matrix theory and related discrete mathematics. Proof files and build instructions are in English. The project pins Lean 4.36.0 and mathlib in the Lake manifest.

## Modular Hadamard matrices

An order $n$ is supported at modulus $m$ if there is a square integer sign matrix of order $n$ $H$ with $HH^{T} = nI$ modulo $m$. For positive odd $m$, let $Q_m(n)$ mean that $n$ is a sum of `gcd(n, 4)` squares modulo $m$.

| Result | Formal statement |
| --- | --- |
| Every arithmetic progression through $n$ contains arbitrarily large supported orders if and only if $Q_m(n)$. | [Integer matrix and square-sum statement](Statements/CompositeSquareNormStatement.lean) |
| For every odd modulus with at most two distinct prime factors, $Q_m(n)$ is necessary and sufficient at each sufficiently large $n$. For any fixed odd modulus the same holds when one of $n,n-1,n-2$ is coprime to it. | [Square-norm theorem](Quantum/Hadamard/CompositeSquareNorms.lean) and [three coprimality conditions](Quantum/Hadamard/ThreeCenterConductor.lean) |
| For any odd prime $p$, the sufficiently large supported orders are exactly the even orders and the orders that are squares modulo $p$, including zero. | [Kuperberg's conjecture in integer-matrix form](Statements/KuperbergStatement.lean) |
| Local obstructions and constructive sufficiency at two odd prime powers, with arbitrary exponents. | [Expanded valuation statements](Statements/TwoPrimePowerSpectrumStatement.lean) |

For example, modulo 45, every order congruent to 6 modulo 180 is excluded by its 3-adic valuation. Every sufficiently large order congruent to 18 modulo 180 is supported since $18=3^2+3^2$. The second conclusion has a threshold depending on the modulus. For moduli with more than two prime divisors, the progression theorem alone does not imply pointwise existence.

The prime statement is formulated in [Kuperberg, *Hadamard matrices modulo p and small modular Hadamard matrices*](https://doi.org/10.1002/jcd.21522). Kline's November 2026 preprint proves the prime criterion for odd primes outside the class 1 modulo 8 and supplies design extensions used in this development. [Kline, *Modular Hadamard matrices at large orders*](https://doi.org/10.5281/zenodo.24421216)

## Conference matrices and determinants

Let $C$ be a symmetric conference matrix of order $n=2v>2$ and let $W_n=(2n-2)(n-2)^{v-1}$ be the Ehlich–Wojtas bound. At every such order there is a diagonal with $v$ plus signs and $v$ minus signs for which $|\det(C+D)|>(\sqrt e/2)W_n$. Writing $q=n-1$, the mean over these balanced diagonals is at least $(q+1/q)^v$. More generally, the coefficient of $z^k$ in $((q-1)(1+z)^2+4z)^v$ is the exact sum of the absolute determinants over all diagonals with $k$ positive entries. [Exact generating function](Quantum/Hadamard/ConferenceDiagonalAverage.lean) · [Balanced mean and existence theorem](Quantum/Hadamard/ConferenceBalancedMean.lean)

For individual completions with a fraction of positive signs tending to $a$, the determinant ratio tends to $\exp(2a(1-a))/2$ as the order grows. At balance the limit is $\sqrt e/2$, and every balanced completion attains at least four fifths of $W_n$ from order 110. The 30 intermediate even orders through 168 are covered by uniform rational moment bounds. For smaller orders starting at 30, one integer inequality involving the cubic trace of the positive principal block suffices. For the Paley matrix, this gives the same bound at every eligible order at least 30 for signings defined by nonsingular projective binary quadratic forms. For the 108 explicit small matrices from 18 fields, Lean checks the full row correlations, the positive principal block and a lower bound for the determinant of the full matrix. Lean reduces every nonsingular form to six signings, verifies the exact field coordinates in all eleven necessary small fields, and transfers their bounds to every finite field of the same size. The theorem covers every eligible order from 30 with opposite signs at the two roots of a split form. [All-order theorem](verification/conference/paley-quadratics/certificates/PaleyAllOrders.lean) · [Independent statement with literal matrix entries](verification/conference/paley-quadratics/certificates/PaleyRawStatement.lean) The four sets used in Theorem 4.1 of Momihara, Suda and Xiang determine the positive and negative entries of two finite Paley blocks. For regular cores with constant sign borders and a near-Hadamard row Gram partition, equality of the two within-class core Gram blocks gives equal absolute determinants when their off-diagonal entries avoid −2. For cores built from two circulant blocks per block row, matching the sum of their sequence autocorrelations suffices. For all four pairings of the signed sets in Theorem 4.1, the sum of their autocorrelations matches one of the two split Paley cores in every finite field under consideration. The block layout and border strips of classes (5) and (6) still need to be matched to the comparison hypotheses, and the connection with class (4) remains open. [Explicit correlations of the four published sets](Quantum/Hadamard/ProjectiveSupportCorrelations.lean) [Border and two-circulant theorems](Quantum/Hadamard/NearHadamardBorders.lean) · [Exact enumeration of borders](verification/conference/paley-quadratics/check_split_borders.py) [Four support identities](Quantum/Hadamard/ProjectiveSplitSupports.lean) · [Original 2022 construction](https://www.sciencedirect.com/science/article/abs/pii/S0024379522003123) · [Survey question](https://arxiv.org/html/2610.27175v2#Thmproblem15) · [Uniform bound from order 110](Quantum/Hadamard/ConferenceShiftedThreshold.lean) · [Cubic trace criterion](Quantum/Hadamard/ConferenceCubicMatrix.lean) · [Determinant on the original projective coordinates](Quantum/Hadamard/ProjectivePaleyDeterminant.lean) · [Quadratic character balance](Quantum/Hadamard/ProjectiveQuadraticBalance.lean) · [108 determinant proofs](verification/conference/paley-quadratics/certificates/) · [How to reproduce the matrices and bounds](verification/conference/paley-quadratics/README.md) · [Independent Lean statements](verification/conference/Statement.lean)

## Other proof families

| Subject | What the formalization establishes | Source |
| --- | --- | --- |
| Exact modular Hadamard orders | Every positive multiple of four is supported at each of moduli 17 and 19. The archive contains the complete Lean sources and finite certificate imports for both moduli. | [Self-contained Lean project](certificates/17-and-19-lean.zip) |
| Quantum Latin squares | For every order at least six, all ray counts from the order to its square are possible except the order plus one. For order six with both diagonals constrained, the precise counts are 6, 8, 10 and 12. | [General theorem](Quantum/Spectrum.lean) · [Order six with diagonal bases](Quantum/DiagonalSixSpectrum.lean) |
| Quantum Sudoku | For each block side at least five, classical clues can admit a quantum solution even when no classical solution exists. A puzzle with one classical completion may also have a continuum of quantum completions. | [Existence counterexamples](Quantum/FractionalPuzzleOrders.lean) · [Uniqueness counterexamples](Quantum/Activated/Family.lean) · [Selected array statements](Statements/QuantumArrays.lean) |
| Bipartite quantum walks | Universal perfect edge transfer characterizes paths among finite connected simple bipartite graphs with at least one edge. An individual forward transfer also has an arithmetic criterion for reverse transfer. | [Path characterization](physics/UniversalBipartiteWalk.lean) · [Reverse transfer](physics/EdgeTransferDecision.lean) |
| Ordinary Hadamard matrix | An explicit construction gives an integer sign matrix with exactly orthogonal rows at order 246,068. | [Integer Gram identity](Quantum/Hadamard/PaleyT246068.lean) · [Skew signed projection at length 271](Quantum/Hadamard/PaleyT271Skew.lean) · [Length 331](Quantum/Hadamard/PaleyT331.lean) |
| Quantum contextuality | In dimension seven an arrangement with 46,656 rays and as many specified orthonormal bases admits transitive actions on each set and a quantum–classical gap. | [Operator identities and classical obstruction](Quantum/FractionalLCSOperators.lean) · [Modular criterion for translated equations](Quantum/FractionalLCSAbelian.lean) |
| Hilbert space projections | A parametrization describes the splittings of two projections. For commuting partial quantum permutation matrices, any completion implies existence of a commuting completion, and uniqueness among commuting completions implies uniqueness among all completions. | [Splittings](Quantum/WeberSplitting.lean) · [Existence](Quantum/WeberCompletion.lean) · [Uniqueness](Quantum/WeberUniqueness.lean) |
| Signed difference sets | For finite abelian groups and $k-\lambda=ps$ with $p$ prime dividing the group order, $p$ coprime to $s$, the classification covers $1\leq s\leq30$. | [Classification](designs/SignedThroughThirty.lean) |
| Complementary sequences | The eight numbered conjectures of Kimberling and Moses are resolved individually, including counterexamples to statements in 6 and 20 and the two readings of the index in 8. | [Combined theorem](sequences/KimberlingSolution.lean) |

## Reproduce the checks

Install [elan](https://github.com/leanprover/elan) and Git. Run these commands from a checkout.

```sh
lake exe cache get
lake build
lake env lean Statements/CompositeSquareNormStatement.lean
lake env lean Statements/TwoPrimePowerSpectrumStatement.lean
lake env lean Statements/KuperbergStatement.lean
lake env leanchecker -v Quantum.Hadamard.CompositeSquareNorms
lake env leanchecker -v Quantum.Hadamard.ConferenceCubicMatrix
```

Use the following targets to build additional results individually. The dense finite certificate for moduli 17 and 19 has its own Lake project inside the linked archive.

~~~sh
lake build Quantum.Spectrum Quantum.DiagonalSixSpectrum
lake build Quantum.Activated.Family Quantum.FractionalPuzzleOrders
lake build Walks
lake build Sequences
lake build Designs
python verification/conference/verify_lean.py
python verification/conference/check_diagonal_averages.py
python verification/conference/paley-quadratics/check_trace.py
python verification/conference/paley-quadratics/check_field_models.py --jobs 3
~~~

The standalone statements print their full theorem types and axiom lists. The square-sum endpoints use `propext`, `Classical.choice`, and `Quot.sound`. The source files include earlier constructions and attribute them in the relevant modules. Computational checking establishes the formal statements under the pinned dependencies. Questions of bibliographic priority and journal review are separate.

AI tools assisted with proofs and exposition. Public theorem names, assumptions, and source files are provided so readers can check them independently.
