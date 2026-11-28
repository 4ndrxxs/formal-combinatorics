# The nine research questions

The links below identify the original statements and the proof files for each question. A counterexample decides a universal conjecture by exhibiting an instance in which it fails.

## 1. Kuperberg’s Conjecture 5.1 on modular Hadamard orders

Which sufficiently large orders admit a modular Hadamard matrix for a fixed odd prime modulus?

The criterion is that the order is even or is a square modulo the prime, including zero.

[Published question](https://arxiv.org/pdf/1409.0148#page=6) · [Lean statement](https://github.com/4ndrxxs/kuperberg-modular-hadamard/blob/main/Statements/KuperbergStatement.lean) · [Proof repository](https://github.com/4ndrxxs/kuperberg-modular-hadamard)

## 2. Problem 15 on the determinants of three near-Hadamard families

Does each of the three published families reach four fifths of the Ehlich–Wojtas bound at every admissible order from 30?

Lean proves the finite-field product bounds for all three families. The matrix corollary takes the three published determinant identities as hypotheses.

[Published question](https://arxiv.org/html/2610.27175v2#Thmproblem15) · [Lean statement](https://github.com/4ndrxxs/near-hadamard-problem-15/blob/main/verification/conference/paley-quadratics/certificates/MSXProblem15Statement.lean) · [Proof repository](https://github.com/4ndrxxs/near-hadamard-problem-15)

## 3. Cardinalities of quantum Latin squares

Which counts of distinct rays occur in a quantum Latin square of order at least six?

Every count from n through n² occurs except n + 1. This includes the outstanding cases at orders 9, 11 and 23 in Table 6.

[Published question](https://arxiv.org/html/2607.19969v2#S5.T6) · [Lean statement](https://github.com/4ndrxxs/quantum-latin-square-spectrum/blob/main/Quantum/Spectrum.lean) · [Proof repository](https://github.com/4ndrxxs/quantum-latin-square-spectrum)

## 4. Nechita–Pillet Conjecture 6 on quantum Sudoku

Must classical clues that have a quantum solution also have a classical solution?

Counterexamples exist for every block side of at least five. The universal implication is false.

[Published question](https://www.rintonpress.com/xxqic21/qic-21-910/0781-0799.pdf#page=7) · [Lean statement](https://github.com/4ndrxxs/quantum-sudoku-existence-conjecture/blob/main/Quantum/FractionalPuzzleOrders.lean) · [Proof repository](https://github.com/4ndrxxs/quantum-sudoku-existence-conjecture)

## 5. Weber’s Problem 3.5 on projection splittings

How can two projections be split into pairs of projections with the specified orthogonality conditions?

A commuting projection gives a parametrization of all splittings on an arbitrary Hilbert space.

[Published question](https://link.springer.com/article/10.1007/s11785-023-01335-x#Sec13) · [Lean statement](https://github.com/4ndrxxs/weber-projection-splittings/blob/main/Quantum/WeberSplitting.lean) · [Proof repository](https://github.com/4ndrxxs/weber-projection-splittings)

## 6. Weber’s Problem 3.6 on quantum permutation completion

Can commuting prescribed entries admit a quantum permutation completion when no commuting completion exists?

For commuting prescribed entries, a completion exists exactly when a commuting completion exists.

[Published question](https://link.springer.com/article/10.1007/s11785-023-01335-x#Sec13) · [Lean statement](https://github.com/4ndrxxs/weber-quantum-permutation-completion/blob/main/Quantum/WeberCompletion.lean) · [Proof repository](https://github.com/4ndrxxs/weber-quantum-permutation-completion)

## 7. Kimberling–Moses Conjecture 6 on complementary sequences

Do the proposed recurrence and residue rules hold for the complementary sequences in Conjecture 6?

The recurrence and initial values for the first sequence hold. Explicit counterexamples disprove the proposed modulus and the recurrence for the second sequence.

[Published question](https://cs.uwaterloo.ca/journals/JIS/VOL24/Kimberling/kimb23.pdf#page=8) · [Lean statement](https://github.com/4ndrxxs/kimberling-moses-conjecture-6/blob/main/sequences/KimberlingGeneral.lean) · [Proof repository](https://github.com/4ndrxxs/kimberling-moses-conjecture-6)

## 8. Kimberling–Moses Conjecture 14 on the offset by two

How does adding two to the defining equation change the first complementary sequence?

The increase is two at multiples of three and one at every other index.

[Published question](https://cs.uwaterloo.ca/journals/JIS/VOL24/Kimberling/kimb23.pdf#page=12) · [Lean statement](https://github.com/4ndrxxs/kimberling-moses-conjecture-14/blob/main/sequences/KimberlingShifts.lean) · [Proof repository](https://github.com/4ndrxxs/kimberling-moses-conjecture-14)

## 9. Chen’s question on universal perfect edge transfer

Can the two-reflection bipartite walk have universal perfect edge transfer when its one-step transition is not a permutation?

Universal transfer forces a permutation. Among finite connected simple bipartite graphs with at least one edge, exactly the paths have universal transfer.

[Published question](https://dspacemainprd01.lib.uwaterloo.ca/server/api/core/bitstreams/4fe72fad-a681-474c-ae1e-8f9749dc0d98/content#page=60) · [Lean statement](https://github.com/4ndrxxs/universal-bipartite-edge-transfer/blob/main/physics/UniversalBipartiteWalk.lean) · [Proof repository](https://github.com/4ndrxxs/universal-bipartite-edge-transfer)

The [research archive](archive/README.md) lists the remaining source packages and their reproducible snapshots.
