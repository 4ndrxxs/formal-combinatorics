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

Over every field of characteristic zero, a square matrix of affine linear forms whose determinant equals the generic five-by-five permanent has size at least **twenty-one**. The only hypothesis on the matrix is the polynomial equality `permanent(X) = det(A + Σ xᵢⱼ Fᵢⱼ)`. Over the complex numbers, Grenet's size-31 construction puts the minimum in the interval **21–31**. [Unrestricted theorem](PermanentTwentyOne.lean) · [Explicit complex statement](PermanentFiveStatement.lean) · [Grenet's construction](https://www-verimag.imag.fr/~grenetb/publis/Gre11.pdf)

Write $h=m-1$ and let $a$ be the codimension of the common kernel $L$ of the two endpoint maps of the normalized quintic pencil. At every centre $y$, the Hessian restricted to $L$ has rank at most $2(h-a)$. The ambient Hessian at each point of $L$ has rank at most $h-a$. Polynomial paths give both inequalities on the same coordinate plane. [Liftable directions and their dimension](QuinticDefect.lean) · [Restriction of the Hessian](QuinticRestricted.lean) · [Limit of the Gram matrix](QuinticRestrictedTorus.lean) · [Simultaneous bounds](PermanentSimultaneous.lean)

The gradient excludes a matching of four occupied cells. With at most thirteen cells, a three-line cover places the support inside one of four boards of size thirteen, up to symmetry. Each board has a nonsingular principal Hessian at an explicit integer centre. Deleting a coordinate drops the rank by at most two. With fourteen or fifteen cells, an ambient Hessian minor of order ten suffices. The five integer inverse certificates can be reproduced with the Python standard library. [Cover argument](PermanentBlockCover.lean) · [Rank under coordinate deletion](PermanentPrincipal.lean) · [Integral certificates and independent calculation](check_quintic_restricted.py)

A size-twenty expression would give at least six mutually isotropic Hessian directions at every centre, all inside the fixed endpoint kernel. After scalar extension to the rational function field and a torus degeneration, this forces a square Gram determinant on each twelve-cell frame containing the pivots. Each of the nine possible boards has a point with a simple zero, which excludes a square. On thirteen cells a supported ambient minor has rank eight, and on fourteen or fifteen cells an ambient minor has rank ten. Together these tests exclude every size through twenty. [Square obstruction](PermanentOddObstruction.lean) · [Nine integral simple-zero certificates](twelve-block-data.json) · [Reduction to the nine boards](PermanentTwelveCover.lean) · [Proof details](twelve-discriminant.md)

Regularity at the origin is also proved in Lean. A linear slice with five coordinates meets the zero set of all twenty-five ambient first partials only at the origin. An integer polynomial certificate expresses eight times each sixth power as a combination of the partials. The proof compares this slice with matrices of corank at least two using a parametrization, a chain of prime ideals and Krull's height theorem. In particular a polynomial matrix representing the permanent must have corank one at the origin. The size bound then uses affine linearity. [Slice and polynomial identity](PermanentSlice.lean) · [Height of a point](DeterminantalHeight.lean) · [Parametrization](DeterminantalParametrization.lean) · [Intersection with the graph](DeterminantalGraph.lean) · [First-order vanishing](DeterminantalColumns.lean) · [Derivative of a determinant](DeterminantalDerivative.lean) · [Exclusion of two zero rows](PermanentOrigin.lean)

The general geometric context appears in Proposition 2.1 of Alper, Bogart and Velasco and in von zur Gathen's codimension bound. A separate integer calculation checks the five polynomial identities, and another verifies rank-ten Hessians on all twenty complete three-line supports and all 300 one-cell deletions. [Regularity, Proposition 2.1](https://arxiv.org/html/1505.02205v1) · [Singular locus, Theorem 4.14](https://arxiv.org/html/2402.17839v2#S4.Thmtheorem14)

```sh
lake build QuinticPermanent
lake env leanchecker -v PermanentTwentyOne
lake env leanchecker -v PermanentFiveStatement
python verification/permanent/check_quintic_endpoint.py
python verification/permanent/check_quintic_slice.py
python verification/permanent/check_quintic_saturation.py
python verification/permanent/check_quintic_restricted.py
python verification/permanent/check_quintic_discriminant.py
python verification/permanent/check_quintic_layout.py
```

## Endpoint directions at size twenty-one

For a hypothetical size-21 expression, the common kernel of its two normalized endpoint maps projects onto all five entries of some input row or column. If that kernel has dimension five, it equals the five-dimensional space supported on a single row or column. The exact minimum size over the complex numbers remains between 21 and 31. [Field theorems](PermanentFullLine.lean) · [Complex endpoint equations](PermanentLineStatement.lean)

The proof specializes rational isotropic spaces and computes a twelve-direction Hessian of Witt index four over a two-variable rational function field. A deletion graph with 29 boards and 90 edges combines this form with ten simple-zero certificates and four ambient minors. [Specialization](RationalIsotropicSpecialization.lean) · [Rectangle calculation](PermanentRectangleBound.lean) · [Finite covering proof](PermanentLineDeletions.lean) · [Ten integral witnesses](line-ten-data.json)

```sh
lake build QuinticPermanent
lake env leanchecker -v PermanentFullLine
lake env leanchecker -v PermanentLineStatement
python verification/permanent/check_quintic_rectangle.py
python verification/permanent/check_quintic_line_cover.py
```

## Possible kernel dimensions and pivot boards

The pivot classification initially gives dimensions 5 through 11 and 15. The degree-fifteen argument below excludes 15. For every ordering by distinct weights of the form $a_i+b_j$, the pivot cells belong to one of twelve types up to row and column permutations and transposition. The test considers 58 boards and uses four integral Hessian minors. These are necessary conditions. [Shapes and dimension theorem](PermanentShapeClassification.lean) · [Twelve models](PermanentShapeBoards.lean) · [Deletion proof](PermanentShapeGraph.lean)

For any sets of rows and columns, the kernel contains at least the smaller of their cardinalities in independent matrices supported on their union. In particular, each of the 25 nine-cell crosses carries a nonzero endpoint relation. [Cross theorem](PermanentCross.lean) · [Complex statement](PermanentEndpointStatement.lean)

For every size, a polynomial matrix with determinant equal to the five-by-five permanent has corank at most one at every input. This recovers the geometric regularity criterion of Alper, Bogart and Velasco in this case. In an affine regular normal form, the internal matrix is nilpotent in every common endpoint-kernel direction. [Polynomial regularity](PermanentUnrestricted.lean) · [Nilpotence](PermanentTransferNilpotent.lean)

```sh
lake build QuinticPermanent
lake env leanchecker -v PermanentShapeClassification
lake env leanchecker -v PermanentEndpointStatement
python verification/permanent/check_quintic_shapes.py
```

## Two-row and three-row kernels

In any size-21 representation, an endpoint kernel of dimension 10 consists of all matrices supported on a fixed pair of rows or a fixed pair of columns. The proof uses five exact cubic identities in the entries of a third row. Assuming dimension 15 forces a full three-row or three-column strip, with $D(z)^4=0$ on it. These two implications enter the contradiction in the next section. The earlier dimension-5 theorem gives the corresponding one-line conclusion. [Two-line theorem](PermanentTenKernel.lean) · [Three-line theorem](PermanentFifteenKernel.lean) · [Uniform fourth power](PermanentFifteenNilpotence.lean) · [Explicit complex statement](PermanentStripStatement.lean)

For any regular affine determinant representing a homogeneous polynomial $f$ of degree $d\ge3$, write $a$ for the rank of its two endpoint maps considered together and $m$ for its size. At every point $z$ in their common kernel, $2(m-1)\ge2a+(d-3)\operatorname{rank}\operatorname{Hess}_z(f)$. [General theorem](PencilHomogeneousRank.lean) · [Dimension argument](PencilMomentFlag.lean)

```sh
lake build QuinticPermanent
lake env leanchecker -v PermanentStripStatement
lake env leanchecker -v PencilHomogeneousRank
python verification/permanent/check_quintic_two_rows.py
```

## Exclusion of the three-row and three-column case

Every size-21 affine representation over a characteristic-zero field admits a normalization with endpoint kernel dimension between 5 and 11 and combined endpoint rank between 14 and 20. The tests are necessary conditions for a size-21 expression. The known numerical bounds over the complex numbers are 21 and 31. [Affine statement](PermanentEndpointInterval.lean) · [Complex statement](PermanentIntervalStatement.lean)

On a hypothetical three-row strip, a rank-ten Hessian forces the successive transfer ranks 15, 10, 5 and 0. An explicit two-parameter slice of the permanent has a complementary Hessian determinant of degree 15 which is irreducible over the rational function field in its second parameter. A linear nilpotent pencil of order 20 with five full four-step chains at infinity must lose that type at a prime of degree at most 14. Applying the two conclusions to the same linear pencil rules out dimension 15. The proof carries the coordinate kernel to every residue field in question. [Exclusion](PermanentFifteenExclusion.lean) · [Small-prime theorem over any field](PencilFourPrime.lean) · [Exact polynomial and slope](PermanentCurveHessian.lean) · [Scalar extension](PermanentBoardScalarExtension.lean)

The internal transfer restricted to the common endpoint kernel is injective for a normalized permanent representation at every order over a field. A complementary matching realizes each coordinate covector as a gradient. [Transfer injectivity](PermanentTransferFaithful.lean) · [Gradient theorem](PermanentCoordinateGradient.lean)

```sh
lake build QuinticPermanent
lake env leanchecker -v PermanentIntervalStatement
lake env leanchecker -v PencilFourPrime
python verification/permanent/check_quintic_hessian_curve.py
```

## Hessian ranks of permanents

A nonzero separately symmetric grid matrix whose entries vanish on equal row or column indices has rank four or at least six. At rank four its entries factor into two symmetrized products, one on row indices and one on column indices. The support refinement applies in characteristic different from two. [Rank gap](HollowGridSmallRank.lean) · [Factorization criterion](HollowGridDisjoint.lean) · [Sharp binary example](HollowGridBinary.lean)

The Hessian of every square permanent satisfies this grid condition. Adjoining a diagonal one to explicit smooth points of orders two and three gives all admissible positive ranks as the order varies. The theorem on the smooth locus requires order at least two. The ambient and hypersurface spectra agree. [Border formula](PermanentHessianSuspension.lean) · [Integral seeds](PermanentSpectrumSeeds.lean) · [All-characteristic statements](PermanentSmoothSpectrum.lean) · [Ambient spectrum](PermanentAmbientSpectrum.lean)

At fixed order three, integral matrices attain every allowed positive rank in characteristic different from two. Each rank certificate uses an integer column-span identity and an inverse of a principal minor after multiplication by a power of two. [Order-three theorem and certificates](PermanentOrderThreeSpectrum.lean)

```sh
lake build PermanentOrderThreeSpectrum PermanentAmbientSpectrum HollowGridDisjoint HollowGridBinary
lake env leanchecker -v PermanentOrderThreeSpectrum
lake env leanchecker -v PermanentSmoothSpectrum
```

## Hessian ranks in order four

The theorem `PermanentOrderFour.all_fields` classifies smooth order-four Hessian ranks over every field. The possible ranks are 4, 6, and 8 through 16 when both 2 and 3 are nonzero, 4, 6, and 8 through 15 in characteristic three, and 8 in characteristic two. The proof of the missing rank seven shows that a smooth zero of rank at most seven has a zero input row or column when 2 is nonzero. At a matrix with a zero line the Hessian has even rank. Three explicit boundary matrices have invertible eight-by-eight principal Hessian submatrices in every characteristic different from two. The order-four witnesses and their integer or finite-field rank certificates are included. [Classification](PermanentFourAllFields.lean) · [Odd-characteristic proof and witnesses](PermanentOrderFourSpectrum.lean) · [Boundary minors](PermanentFourTemplates.lean)

In characteristic two the permanent is the determinant. At every smooth zero of order `n ≥ 2`, its Hessian has rank exactly `2n`. The proof uses left and right changes of basis, equivalence to the corank-one normal form, and the Hessian rank at a diagonal representative. [Fixed-order theorem](PermanentBinaryFixedOrder.lean) · [Linear substitution](PolynomialLinearHessian.lean) · [Determinant action](DeterminantHessianAction.lean)

```sh
lake build PermanentFourAllFields
lake env leanchecker -v PermanentFourAllFields
lake env leanchecker -v PermanentBinaryFixedOrder
```

## The Bedi–Suagee Hessian rank formula

For the order-`m` arrow matrix with identity core, ones on both strips, and corner `1 − m`, the permanent vanishes and its corner derivative is one. In every field of characteristic different from two, the ordinary Hessian has rank exactly `m² − m + 2` for all `m ≥ 2`. Bedi and Suagee recorded this formula as a numerical observation for orders 3 through 25 in Remark 2.2.18 of their ECCC report. [Original remark](https://eccc.weizmann.ac.il/report/2024/015/download/) · [Lean theorem](PermanentArrowRank.lean)

The radical consists of variations whose core is diagonal, whose two strips equal that diagonal, and whose corner and diagonal sum vanish. Attaching a new ordinary index preserves every old Hessian entry. This reduces the entry calculation to matrices of order at most five. The kernel calculation and rank-nullity argument hold at arbitrary order. [Leaf identity](PermanentArrowLeaf.lean) · [Uniform entries](PermanentArrowEntries.lean) · [Kernel](PermanentArrowKernel.lean)

```sh
lake build PermanentArrowRank
lake env leanchecker -v PermanentArrowRank
```
