# Research questions and proof repositories

All 41 research questions have independently cloneable Git repositories. The table links the 15 hosted project pages currently verified on GitHub. Every row also has a complete portable Git repository, including its English README and build instructions.

To use a portable copy, download the bundle and clone it locally. For example,

~~~sh
git clone kimberling-moses-conjecture-14.bundle kimberling-moses-conjecture-14
~~~

The [download manifest](https://github.com/4ndrxxs/formal-combinatorics/blob/standalone-bundles/manifest.json) records each SHA-256 hash and its checkout’s Git tree hash. The [original source branch](https://github.com/4ndrxxs/formal-combinatorics/tree/legacy-monorepo) preserves the complete public collection and its commit history.

## Permanents and algebraic complexity

| Question | Result type | Proof | Portable repository |
| --- | --- | --- | --- |
| Determinantal complexity of the five-by-five permanent | Partial result | [Project page](https://github.com/4ndrxxs/permanent-five-determinantal-complexity) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/permanent-five-determinantal-complexity.bundle) |
| Determinant and permanent coefficient signs | Theorem | [Project page](https://github.com/4ndrxxs/permanent-determinant-coefficient-signs) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/permanent-determinant-coefficient-signs.bundle) |
| Hessian rank spectra of permanents | Theorem | [Project page](https://github.com/4ndrxxs/permanent-hessian-rank-spectrum) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/permanent-hessian-rank-spectrum.bundle) |
| Maximum Hessian rank at a smooth permanent zero | Theorem | [Project page](https://github.com/4ndrxxs/permanent-maximum-hessian-rank) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/permanent-maximum-hessian-rank.bundle) |
| The Bedi–Suagee arrow-matrix Hessian rank | Theorem | [Project page](https://github.com/4ndrxxs/bedi-suagee-arrow-hessian) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/bedi-suagee-arrow-hessian.bundle) |

## Hadamard matrices and determinants

| Question | Result type | Proof | Portable repository |
| --- | --- | --- | --- |
| Problem 15 on the determinants of three near-Hadamard families | Theorem | [Project page](https://github.com/4ndrxxs/near-hadamard-problem-15) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/near-hadamard-problem-15.bundle) |
| Determinants of diagonal sign completions of symmetric conference matrices | Theorem | [Project page](https://github.com/4ndrxxs/conference-diagonal-determinants) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/conference-diagonal-determinants.bundle) |
| Quadratic signings of the Paley conference matrix | Theorem | [Project page](https://github.com/4ndrxxs/paley-quadratic-signings) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/paley-quadratic-signings.bundle) |
| Kuperberg’s Conjecture 5.1 on modular Hadamard matrices | Theorem | [Project page](https://github.com/4ndrxxs/kuperberg-modular-hadamard) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/kuperberg-modular-hadamard.bundle) |
| Eventual orders of modular Hadamard matrices at composite moduli | Partial result | [Project page](https://github.com/4ndrxxs/modular-hadamard-composite-orders) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/modular-hadamard-composite-orders.bundle) |
| Modular Hadamard orders in arithmetic progressions | Theorem | [Project page](https://github.com/4ndrxxs/modular-hadamard-progressions) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/modular-hadamard-progressions.bundle) |
| Modular Hadamard matrices at every order divisible by four for moduli 17 and 19 | Theorem | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/certificates/17-and-19-lean.zip) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/modular-hadamard-17-19.bundle) |
| Periodic circulant T-systems of orders 271 and 331 | Construction | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/Quantum/Hadamard/PaleyT271.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/periodic-circulant-t-systems.bundle) |
| An ordinary Hadamard matrix of order 246,068 | Construction | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/Quantum/Hadamard/PaleyT246068.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/hadamard-order-246068.bundle) |

## Quantum Latin squares and hypercubes

| Question | Result type | Proof | Portable repository |
| --- | --- | --- | --- |
| Ray counts in quantum Latin squares | Theorem | [Project page](https://github.com/4ndrxxs/quantum-latin-square-spectrum) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/quantum-latin-square-spectrum.bundle) |
| Exceptional orders of diagonal quantum Latin squares | Theorem | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/Quantum/DiagonalSixSpectrum.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/diagonal-quantum-latin-squares.bundle) |
| Existence of pandiagonal quantum Latin squares | Partial result | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/Quantum/Pandiagonal.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/pandiagonal-quantum-latin-squares.bundle) |
| Ray counts in small symmetric quantum Latin squares | Theorem | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/Quantum/SymmetricSpectrum.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/symmetric-quantum-latin-squares.bundle) |
| Maximal quantum Latin hypercubes | Construction | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/Quantum/MaximalHypercubes.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/maximal-quantum-latin-hypercubes.bundle) |

## Quantum Sudoku, measurements and contextuality

| Question | Result type | Proof | Portable repository |
| --- | --- | --- | --- |
| Ray counts in quantum Sudoku | Partial result | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/Quantum/SudokuSpectrum.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/quantum-sudoku-cardinality-spectrum.bundle) |
| Quantum Sudoku completion from classical clues | Counterexample | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/Quantum/FractionalPuzzleOrders.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/quantum-sudoku-existence-conjecture.bundle) |
| Quantum Sudoku uniqueness from classical clues | Counterexample | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/Quantum/Activated/Family.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/quantum-sudoku-uniqueness-conjecture.bundle) |
| Reconstructing quantum Sudoku from complete blocks | Theorem | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/Quantum/SudokuBlocks.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/quantum-sudoku-block-reconstruction.bundle) |
| Quantum Sudoku measured in its first block | Counterexample | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/Quantum/FractionalBlockAll.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/quantum-sudoku-block-measurements.bundle) |
| The single-basis measurement image of quantum Sudoku | Theorem | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/Quantum/FractionalPolygons.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/fractional-sudoku-measurement-image.bundle) |
| Transitive contextuality in prime dimension | Construction | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/Quantum/FractionalLCSOperators.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/transitive-quantum-contextuality.bundle) |

## Weber’s questions on quantum permutations

| Question | Result type | Proof | Portable repository |
| --- | --- | --- | --- |
| Weber’s two-projection splitting problem | Theorem | [Project page](https://github.com/4ndrxxs/weber-projection-splittings) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/weber-projection-splittings.bundle) |
| Weber’s quantum permutation completion problem | Theorem | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/Quantum/WeberCompletion.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/weber-quantum-permutation-completion.bundle) |

## Kimberling–Moses sequence conjectures

| Question | Result type | Proof | Portable repository |
| --- | --- | --- | --- |
| Kimberling–Moses Conjecture 6 on dilated subscripts | Counterexample | [Project page](https://github.com/4ndrxxs/kimberling-moses-conjecture-6) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/kimberling-moses-conjecture-6.bundle) |
| Kimberling–Moses Conjecture 8 on upper indices | Theorem | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/sequences/KimberlingIrregular.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/kimberling-moses-conjecture-8.bundle) |
| Kimberling–Moses Conjecture 14 on offset two | Theorem | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/sequences/KimberlingShifts.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/kimberling-moses-conjecture-14.bundle) |
| Kimberling–Moses Conjecture 15 on offset three | Theorem | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/sequences/KimberlingShifts.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/kimberling-moses-conjecture-15.bundle) |
| Kimberling–Moses Conjecture 16 on offset five | Theorem | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/sequences/KimberlingShifts.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/kimberling-moses-conjecture-16.bundle) |
| Kimberling–Moses Conjecture 18 on gaps between good indices | Theorem | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/sequences/KimberlingGaps.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/kimberling-moses-conjecture-18.bundle) |
| Kimberling–Moses Conjecture 19 on the density of good indices | Theorem | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/sequences/KimberlingDensity.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/kimberling-moses-conjecture-19.bundle) |
| Kimberling–Moses Conjecture 20 on the offset threshold for uniqueness | Counterexample | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/sequences/KimberlingThreshold.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/kimberling-moses-conjecture-20.bundle) |

## Quantum walks on bipartite graphs

| Question | Result type | Proof | Portable repository |
| --- | --- | --- | --- |
| Universal perfect edge transfer in bipartite quantum walks | Theorem | [Project page](https://github.com/4ndrxxs/universal-bipartite-edge-transfer) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/universal-bipartite-edge-transfer.bundle) |
| Reversibility of perfect edge transfer | Theorem | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/physics/EdgeTransferDecision.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/reverse-bipartite-edge-transfer.bundle) |
| Edge cuts and perfect transfer at minimum degree three | Partial result | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/physics/EdgeCutWalk.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/bipartite-edge-transfer-cuts.bundle) |

## Signed difference sets

| Question | Result type | Proof | Portable repository |
| --- | --- | --- | --- |
| Signed difference sets with norm cofactor at most 30 | Theorem | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/designs/SignedThroughThirty.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/signed-difference-set-cofactors.bundle) |
| A product construction for signed difference sets | Construction | [Original proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/designs/SignedProduct.lean) | [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/standalone-bundles/projects/signed-difference-set-product.bundle) |

## How related questions fit together

- **Permanent.** The five-by-five lower bound is 21 over every characteristic-zero field. The bound of 31 over the complex numbers comes from Grenet’s construction. The rank spectrum project ranges over orders and includes separate small-order classifications. The maximum-rank project fixes the order and asks for the largest rank at a smooth zero over an infinite field. [General lower-bound proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/verification/permanent/PermanentTwentyOne.lean) · [Grenet’s construction](https://www-verimag.imag.fr/~grenetb/publis/Gre11.pdf)
- **Hadamard matrices.** The prime-modulus and composite-modulus projects classify individual sufficiently large orders under their stated hypotheses. The arithmetic-progression theorem asks whether every progression through a number contains arbitrarily large supported orders. The moduli 17 and 19 project covers every positive multiple of four, including the small orders. Its endpoints are 'HadamardMod.seventeen_all_integer' and 'HadamardMod.nineteen_all_integer'.
- **Near-Hadamard Problem 15.** The published question starts at order 30. Lean proves the finite-field product bounds for all three families in that range. The matrix corollary takes the three published determinant identities as explicit hypotheses. [Published problem](https://arxiv.org/html/2610.27175v2#Thmproblem15) · [Lean statement](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/verification/conference/paley-quadratics/certificates/MSXProblem15Statement.lean)
- **Complementary sequences.** Kimberling–Moses Conjectures 14, 15 and 16 are separately numbered in the paper. They compare offsets 2, 3 and 5 using a shared construction. Conjectures 18 and 19 study gaps and density in a common index set. [Published conjectures](https://cs.uwaterloo.ca/journals/JIS/VOL24/Kimberling/kimb23.pdf) · [Shared shift proof](https://github.com/4ndrxxs/formal-combinatorics/blob/1024b8d59eca29300691c87cb92c1c1fa51940c6/sequences/KimberlingShifts.lean)
- **Quantum permutations.** Weber’s Problem 3.5 asks how a pair of projections splits. Problem 3.6 asks for existence and uniqueness of a completion of a partly specified quantum permutation. Each has its own formal statement.
