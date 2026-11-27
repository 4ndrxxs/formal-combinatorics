# Quadratic signings of the Paley conference matrix

For each prime power (q) congruent to one modulo four, index the matrix by the finite field and a point at infinity. Its finite entries are the quadratic character of the difference of the points. Its border entries are positive and its diagonal is zero. The three positive sets in this check are the nonzero squares together with zero, the nonsquares together with zero, and the finite points where the character of x²−d is negative, for a fixed nonsquare d. Each complement is included. The two possible nonsplit orientations may exchange labels when the field model or d changes.

The file determinants.csv gives 384 exact determinants and Ehlich–Wojtas bounds at the 64 eligible prime powers from 29 through 673. Run the following commands in the directory containing this file.

~~~sh
python check_projective.py
python check_trace.py
uv run --no-project --with python-flint python finite_check.py --jobs 3 --output determinants.csv
~~~

The first standard-library program verifies table coverage, the exact ratio inequalities, and the split symmetries. At q=29 it independently checks all projective sign orbits and the determinants of their representatives. The second program constructs the fields below q=169 by polynomial arithmetic, checks an entire multiplicative cycle, computes each cubic trace both by a signed triangle count and by Hamming distances, and verifies all 108 determinants by integer Bareiss elimination. Append `--output traces.json` to regenerate the replayable small-field record. The FLINT program in the third command reconstructs the full 384-entry table from independent field models.

These files concern the six explicitly defined signings. Comparing them with the particular matrices in Momihara, Suda and Xiang, Theorem 1.6, requires a construction-level identification.
