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

Let a homogeneous quintic in $N$ variables equal the determinant of an $m$ by $m$ matrix of affine linear forms. Assume the constant matrix has rank $m-1$. There is a fixed subspace $L$ on which the polynomial vanishes to order at least two along every line through each point. Its Hessian at each $z$ in $L$ satisfies the following inequality.

```text
codimension(L) + rank(Hessian at z) ≤ m − 1
```

The Lean theorem works over every field and accepts arbitrary affine coefficients. Constant changes of bases isolate the invertible block. Homogeneity forces the scalar linear entry in the remaining corner to vanish. The Hessian is specified by extracting the mixed coefficient of two independent direction variables. [Theorem and basis changes](QuinticRegular.lean) · [Removal of the linear corner](QuinticCorner.lean) · [Normalized pencil theorem](QuinticKernel.lean)

The proof computes the mixed determinant coefficient using a Schur complement, including the scalar determinant prefactor. Homogeneity then turns the entire series into a single monomial. A bilinear rank argument gives the inequality. [Schur complement](QuinticPencil.lean) · [Homogeneity](QuinticHomogeneous.lean) · [Normalized affine identity](QuinticAffine.lean) · [Rank deduction](QuinticRank.lean) · [Linear algebra](QuinticEndpoint.lean)

The application to the complex permanent of order five also requires a proof that all representations of this particular permanent have corank one at the origin, a coordinate degeneration, and the matching and Hessian arguments on the limiting supports. The Python calculation checks the finite examples by directly differentiating every permanent monomial. The complete numerical lower bound of sixteen is still under formalization.

```sh
lake build QuinticPermanent
lake env leanchecker -v QuinticRegular
python verification/permanent/check_quintic_endpoint.py
```
