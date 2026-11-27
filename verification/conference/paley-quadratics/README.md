# Quadratic signings of the Paley conference matrix

For each prime power (q) congruent to one modulo four, index the matrix by the finite field and a point at infinity. Its finite entries are the quadratic character of the difference of the points. Its border entries are positive and its diagonal is zero. The three positive sets in this check are the nonzero squares together with zero, the nonsquares together with zero, and the finite points where the character of x²−d is negative, for a fixed nonsquare d. Each complement is included. The two possible nonsplit orientations may exchange labels when the field model or d changes.

The file determinants.csv gives 384 exact determinants and Ehlich–Wojtas bounds at the 64 eligible prime powers from 29 through 673. Run the following commands in the directory containing this file.

~~~sh
python check_projective.py
python check_trace.py
uv run --no-project --with python-flint python finite_check.py --jobs 3 --output determinants.csv
~~~

The first standard-library program verifies table coverage, the exact ratio inequalities, and the split symmetries. At q=29 it independently checks all projective sign orbits and the determinants of their representatives. The second program constructs the fields below q=169 by polynomial arithmetic, checks an entire multiplicative cycle, computes each cubic trace both by a signed triangle count and by Hamming distances, and verifies all 108 determinants by integer Bareiss elimination. Append `--output traces.json` to regenerate the replayable small-field record. The FLINT program in the third command reconstructs the full 384-entry table from independent field models.

The first eleven fields, through q=101, cover all orders below the uniform theorem starting at order 110. The other seven fields give a second proof for their six explicit matrices.

The [Lean sources for the 18 fields](certificates/) contain the full matrices as binary rows and six determinant theorems per field. Each theorem has no hypotheses. Its proof checks every row correlation of the full matrix, the permutation putting the positive points first, the entries of the selected principal block, and its exact cubic trace. The four-fifths inequality concerns the determinant of the full completed matrix. The standard-library field code supplies the numbered polynomial coordinates and their interpretation as Paley entries.

To regenerate the sources and replay all 108 determinant proofs, run `python check_lean_traces.py` after `lake exe cache get` in the Lean project. The checker compares the generated code with the distributed source, checks the reported axioms, and runs `leanchecker` on every module. Use `--q 29` for the six proofs at order 30, `--jobs 3` to check three fields concurrently, or `--project PATH` to select a matching pinned Lake installation.

These files concern the six explicitly defined signings. Comparing them with the particular matrices in Momihara, Suda and Xiang, Theorem 1.6, requires a construction-level identification.
