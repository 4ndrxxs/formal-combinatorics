# Supporting results and archived projects

The eleven projects below retain the proofs from their original public repositories. The links include each repository, a Git bundle that can be cloned offline, and the mathematical scope of the result.

## Permanent and Hessian results

| Result | Scope | Files |
| --- | --- | --- |
| Determinantal complexity of the five-by-five permanent | The lower bound is 21 in characteristic zero. The exact minimum over the complex numbers remains between 21 and 31. | [GitHub](https://github.com/4ndrxxs/permanent-five-determinantal-complexity) · [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/permanent-five-determinantal-complexity.bundle) |
| Determinant and permanent coefficient signs | For a two-part partition, row and column signs identify the coefficient matrices over any commutative ring. At every order from four, a three-part partition obstructs arbitrary local reweighting in characteristic different from two. | [GitHub](https://github.com/4ndrxxs/permanent-determinant-coefficient-signs) · [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/permanent-determinant-coefficient-signs.bundle) |
| Hessian rank spectra of permanents | The spectrum across orders is classified in each characteristic, including the smooth locus. Separate theorems give the fixed-order spectra at orders three and four and the fixed-order rank in characteristic two. | [GitHub](https://github.com/4ndrxxs/permanent-hessian-rank-spectrum) · [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/permanent-hessian-rank-spectrum.bundle) |
| Maximum Hessian rank at a smooth permanent zero | For m at least two the maximum is m squared if both 2 and m minus 1 are nonzero, m squared minus one in odd characteristic dividing m minus one, and 2m in characteristic two. The characteristic-zero full-rank result is due to Mignon and Ressayre. | [GitHub](https://github.com/4ndrxxs/permanent-maximum-hessian-rank) · [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/permanent-maximum-hessian-rank.bundle) |
| The Bedi–Suagee arrow-matrix Hessian rank | For every order m at least two over a field of characteristic different from two, the Hessian rank of the Bedi–Suagee arrow matrix is m squared minus m plus two. | [GitHub](https://github.com/4ndrxxs/bedi-suagee-arrow-hessian) · [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/bedi-suagee-arrow-hessian.bundle) |

## Conference and near-Hadamard matrices

| Result | Scope | Files |
| --- | --- | --- |
| Determinants of diagonal sign completions of symmetric conference matrices | At every even order n > 2 admitting a symmetric conference matrix, some balanced signing exceeds √e/2 times the Ehlich–Wojtas bound. Every balanced signing attains at least four fifths of that bound from order 110. An exact generating function gives the determinant total for each sign count. As n grows and the positive-sign proportion tends to a, the determinant divided by the bound tends to exp(2a(1−a))/2. | [GitHub](https://github.com/4ndrxxs/conference-diagonal-determinants) · [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/conference-diagonal-determinants.bundle) |
| Quadratic signings of the Paley conference matrix | Yes for every finite field of order q ≥ 29 with q ≡ 1 modulo 4 and either orientation away from the roots. The proof reduces the forms to six signings and handles the eleven field orders below the uniform conference-matrix bound. The supplementary certificates check 108 explicit completed matrices over 18 fields. | [GitHub](https://github.com/4ndrxxs/paley-quadratic-signings) · [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/paley-quadratic-signings.bundle) |

## Further modular Hadamard results

| Result | Scope | Files |
| --- | --- | --- |
| Eventual orders of modular Hadamard matrices at composite moduli | For m with at most two distinct prime divisors, including arbitrary prime powers, the criterion is that n be a sum of gcd(n,4) squares modulo m. For any odd m it holds when one of n, n−1 and n−2 is coprime to m. At three prime divisors every sufficiently large multiple of 16 is supported, with stronger divisibility results under additional prime conditions. The unrestricted pointwise classification for three or more prime divisors remains open in this project. | [GitHub](https://github.com/4ndrxxs/modular-hadamard-composite-orders) · [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/modular-hadamard-composite-orders.bundle) |
| Modular Hadamard orders in arithmetic progressions | This happens exactly when n is congruent modulo m to a sum of gcd(n,4) squares. For an individual progression n modulo A with A > 0, arbitrarily large odd supported orders occur exactly when A or n is odd and n is a square modulo gcd(A,m). | [GitHub](https://github.com/4ndrxxs/modular-hadamard-progressions) · [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/modular-hadamard-progressions.bundle) |
| Modular Hadamard matrices at every order divisible by four for moduli 17 and 19 | Yes. The two Lean theorems construct integer sign matrices of order 4k for every natural k, with Gram matrix congruent to 4kI modulo 17 and modulo 19, respectively. The original certificate archive contains the two proof modules, their finite starting matrices and a pinned Lake project. | [GitHub](https://github.com/4ndrxxs/modular-hadamard-17-19) · [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/modular-hadamard-17-19.bundle) |

## Signed difference sets

| Result | Scope | Files |
| --- | --- | --- |
| Signed difference sets with norm cofactor at most 30 | Existence is equivalent to $s=1$, an odd prime group order $p$, $k=p-1$ and $\lambda=-1$. The quadratic character realizes these parameters. A separate sieve also rules out $s=33$ and $s=66$. | [GitHub](https://github.com/4ndrxxs/signed-difference-set-cofactors) · [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/signed-difference-set-cofactors.bundle) |

## Other preserved proof packages

These twenty-one packages were distributed as portable Git repositories during the original split. Each download contains its own complete checkout.

- Periodic circulant T-systems of orders 271 and 331. [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/periodic-circulant-t-systems.bundle)
- An ordinary Hadamard matrix of order 246,068. [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/hadamard-order-246068.bundle)
- Exceptional orders of diagonal quantum Latin squares. [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/diagonal-quantum-latin-squares.bundle)
- Existence of pandiagonal quantum Latin squares. [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/pandiagonal-quantum-latin-squares.bundle)
- Ray counts in small symmetric quantum Latin squares. [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/symmetric-quantum-latin-squares.bundle)
- Maximal quantum Latin hypercubes. [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/maximal-quantum-latin-hypercubes.bundle)
- Ray counts in quantum Sudoku. [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/quantum-sudoku-cardinality-spectrum.bundle)
- Quantum Sudoku uniqueness from classical clues. [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/quantum-sudoku-uniqueness-conjecture.bundle)
- Reconstructing quantum Sudoku from complete blocks. [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/quantum-sudoku-block-reconstruction.bundle)
- Quantum Sudoku measured in its first block. [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/quantum-sudoku-block-measurements.bundle)
- The single-basis measurement image of quantum Sudoku. [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/fractional-sudoku-measurement-image.bundle)
- Transitive contextuality in prime dimension. [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/transitive-quantum-contextuality.bundle)
- Kimberling–Moses Conjecture 8 on upper indices. [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/kimberling-moses-conjecture-8.bundle)
- Kimberling–Moses Conjecture 15 on offset three. [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/kimberling-moses-conjecture-15.bundle)
- Kimberling–Moses Conjecture 16 on offset five. [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/kimberling-moses-conjecture-16.bundle)
- Kimberling–Moses Conjecture 18 on gaps between good indices. [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/kimberling-moses-conjecture-18.bundle)
- Kimberling–Moses Conjecture 19 on the density of good indices. [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/kimberling-moses-conjecture-19.bundle)
- Kimberling–Moses Conjecture 20 on the offset threshold for uniqueness. [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/kimberling-moses-conjecture-20.bundle)
- Reversibility of perfect edge transfer. [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/reverse-bipartite-edge-transfer.bundle)
- Edge cuts and perfect transfer at minimum degree three. [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/bipartite-edge-transfer-cuts.bundle)
- A product construction for signed difference sets. [Git bundle](https://raw.githubusercontent.com/4ndrxxs/formal-combinatorics/e6447e4e00188bde7902371dfd707d7c0af6f778/projects/signed-difference-set-product.bundle)

## Checking the archive

Download a bundle and clone it locally. For example,

~~~sh
git clone permanent-five-determinantal-complexity.bundle permanent-five-determinantal-complexity
~~~

The [checksum manifest](https://github.com/4ndrxxs/formal-combinatorics/blob/e6447e4e00188bde7902371dfd707d7c0af6f778/manifest.json) records SHA-256 and Git tree hashes. The [original complete source tree](https://github.com/4ndrxxs/formal-combinatorics/tree/1024b8d59eca29300691c87cb92c1c1fa51940c6) and [its earlier history](https://github.com/4ndrxxs/formal-combinatorics/commits/legacy-monorepo/) are available at their original commits.

The [nine active problem repositories](../README.md) have individual statements and reproduction instructions.
