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

## The permanent of order five

Over every field of characteristic zero, every affine determinantal expression for the generic five-by-five permanent has size at least **sixteen**. For arbitrary constant matrix $A$ and coefficient matrices $F_{ij}$, the sole hypothesis of `PermanentFive.determinantal_lower_bound` is the polynomial equality
`permanent(X) = det(A + Σ xᵢⱼ Fᵢⱼ)`. Its conclusion is `16 ≤ Fintype.card n`, where `n` indexes the rows and columns of the representation. Both polynomials use Mathlib's definitions. The theorem rules out sizes through fifteen. Whether sixteen is attainable remains open in this work. [Unrestricted theorem and normalization](PermanentUnrestricted.lean) · [Lower bound for regular representations](PermanentLowerBound.lean)

The proof rewrites the mixed derivative as the symbolic Hessian. It degenerates the subspace in the quintic estimate to a coordinate subspace and preserves the vanishing of the gradient and the Hessian minors. Every large support then either contains four matching cells or contains explicit points whose Hessian ranks violate the estimate. The finite witnesses are checked by the Lean kernel. [Derivatives](QuinticDerivatives.lean) · [Coordinate degeneration](PermanentDegeneration.lean) · [Hessian rank under degeneration](QuinticTorus.lean) · [Application to the generic permanent](PermanentFive.lean) · [Support counting](PermanentSupports.lean) · [Finite minors](PermanentWitnesses.lean) · [Symmetries](PermanentSymmetry.lean)

Regularity at the origin is also proved in Lean. A linear slice with five coordinates meets the zero set of all twenty-five ambient first partials only at the origin. An integer polynomial certificate expresses eight times each sixth power as a combination of the partials. The proof compares this slice with matrices of corank at least two using a parametrization, a chain of prime ideals and Krull's height theorem. In particular a polynomial matrix representing the permanent must have corank one at the origin. The size bound then uses affine linearity. [Slice and polynomial identity](PermanentSlice.lean) · [Height of a point](DeterminantalHeight.lean) · [Parametrization](DeterminantalParametrization.lean) · [Intersection with the graph](DeterminantalGraph.lean) · [First-order vanishing](DeterminantalColumns.lean) · [Derivative of a determinant](DeterminantalDerivative.lean) · [Exclusion of two zero rows](PermanentOrigin.lean)

The general geometric context appears in Proposition 2.1 of Alper, Bogart and Velasco and in von zur Gathen's codimension bound. A separate integer calculation checks the five polynomial identities, and another verifies rank-ten Hessians on all twenty complete three-line supports and all 300 one-cell deletions. [Regularity, Proposition 2.1](https://arxiv.org/html/1505.02205v1) · [Singular locus, Theorem 4.14](https://arxiv.org/html/2402.17839v2#S4.Thmtheorem14)

```sh
lake build QuinticPermanent
lake env leanchecker -v PermanentUnrestricted
python verification/permanent/check_quintic_endpoint.py
python verification/permanent/check_quintic_slice.py
```
