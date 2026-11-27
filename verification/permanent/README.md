# Local reweighting of the determinant and permanent

A variable of the generic matrix corresponds to an edge between its row and column. For a cut into two colours, index rows by every subset of the first colour and columns by every subset of the second colour. The entry is the coefficient of the corresponding squarefree monomial in the polynomial.

Over any commutative ring the two coefficient matrices differ by independent row and column signs. Their ranks over any field agree. Their transpose Gram matrices have the same characteristic polynomial, so their real singular values agree with multiplicity. The proofs use Mathlib's determinant and permanent of the generic multivariate polynomial matrix. [Formal statements](PermanentCoefficientSigns.lean)

For three colours, allow one arbitrary field scalar for each local monomial in each colour and multiply the three scalars. The grid below admits no such weighting that reproduces the determinant signs over a field of characteristic other than two. This property persists after padding the grid by zeros to any larger size. No three-by-three submatrix of the padded grid has three rows or columns of distinct constant colours. [Formal statements and ten-permutation certificate](PermanentThreeColour.lean)

```text
2 1 1 2
2 0 1 2
1 0 1 1
0 0 0 0
```

Run the following commands from the repository root.

```sh
lake build PermanentCuts
lake env leanchecker -v PermanentCoefficientSigns
lake env leanchecker -v PermanentThreeColour
python verification/permanent/check_coefficient_partitions.py
```

The finite checker covers every binary colouring through order four and all 19,683 three-colourings in order three. These results concern weights attached to the original variables' local monomials. The affine determinantal complexity of the permanent permits arbitrary mixtures of inputs in a matrix of another size.

## Quintic affine determinants

Let a homogeneous quintic in $N$ variables equal the determinant of a normalized pencil with top blocks $0,-b$ and bottom blocks $c,I-D$. Let $h$ be the order of the lower right block and $L$ the common kernel of the row and column forms. At every point $z$ in $L$, the polynomial vanishes to order at least two along every line through $z$. Its Hessian at $z$ satisfies the following inequality.

```text
codimension(L) + rank(Hessian at z) ≤ h
```

The Lean statement uses equality of multivariate polynomials and defines the mixed derivative by extracting the coefficient of the two direction variables. It holds over every field. [Kernel and Hessian theorem](QuinticKernel.lean)

The proof computes the mixed determinant coefficient using a Schur complement, including the scalar determinant prefactor. Homogeneity then turns the entire series into a single monomial. A bilinear rank argument gives the inequality. [Schur complement](QuinticPencil.lean) · [Homogeneity](QuinticHomogeneous.lean) · [Normalized affine identity](QuinticAffine.lean) · [Rank deduction](QuinticRank.lean) · [Linear algebra](QuinticEndpoint.lean)

The application to the complex permanent of order five also requires the reduction of arbitrary representations to this block form, a coordinate degeneration, and the matching and Hessian arguments on the limiting supports. The Python calculation checks the finite examples by directly differentiating every permanent monomial. The complete numerical lower bound of sixteen is still under formalization.

```sh
lake build QuinticPermanent
lake env leanchecker -v QuinticKernel
python verification/permanent/check_quintic_endpoint.py
```
