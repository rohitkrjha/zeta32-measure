FORMALIZATION OF A BOUND FOR ζ(3) − rζ(2)
========================================

Author of the quantitative extension: Rohit Kumar Jha.
Developed with substantial assistance from OpenAI Codex.

MATHEMATICAL STATEMENTS

For every fixed rational r:

    θᵣ = ζ(3) − r ζ(2),

    2 ≤ μ(θᵣ) ≤ 10,000.

All rational approximants of sufficiently large reduced denominator q
satisfy |θᵣ − a/q| > q^(−10000). The threshold may depend on r.
This is not a simultaneous measure for arbitrarily varying coefficients.
The case r=0 is not a new finite-bound result and has much better known bounds.

FINAL THEOREMS

    Zeta32Extension.denominator_bound
    Zeta32Extension.irrationalityExponent_bounds

Both take only the rational parameter r. The denominator theorem discharges
the local-decay premise using local_decay from DirectStability.lean. A separate
minor-based conditional theorem is not used to prove either endpoint.
The real-valued exponent is used only after proving its defining
approximation-exponent set nonempty and bounded above.

SOURCE MAP

  PositiveEnergy, PositiveEndpoint, GramDeterminant
      Positive multiple-integral bound and exact Gram determinant identity.
  WeightLower, PolynomialConditioning, WeightedQuadratic, GramQuadratic
      Exponential lower bound for the actual Gram quadratic form.
  SlopeGrowth, Pencil
      Residue estimate and normalization of the entire rational pencil.
  SignedBilinear, GramComparison, BilinearPerturbation, DirectStability
      Signed moment identity, determinant comparison, and local decay.
  PrimeWindow, ConditionalExponent, UnconditionalExponent, ExponentCorollary
      Prime selection, denominator bound, and exponent semantics.
  Verification.lean and VerifyZeta32Components.lean
      Explicit theorem audit and fresh-kernel dependency replay.

PINNED SOURCES

Lean:     v4.35.0-rc3 (470d5ce1400764999581fd26d5d72b00d990b0f4)
Mathlib:  c55e6e786f49471c72fbddbec5415808896aec1e
Upstream: https://github.com/dtq1997/zeta2-zeta3-linear-independence
Revision: 669c92bf7a3728e0de9ad80c373bc29fb5ca3d58

Tang's unmodified Zeta32 mathematical sources, root module, and Solution are
included. His qualitative theorem, primitive-content estimates, prime-edge
nonvanishing, and energy construction are essential credited inputs.
Tang in turn credits Fauzan's determinant method and other formal libraries.
The upstream NOTICE, LICENSE, and transitive license files are retained.
The upstream Challenge.lean exercise template is excluded; it has deliberate
proof holes and is not imported by the checked solution or extension.

PositiveEnergy adapts the upstream energy proof to retain its positive
integral. Polynomial conditioning builds on the earlier Catalan extension.
GramComparison and ExponentCorollary adapt the explicitly identified general
Hilbert determinant / approximation-set lemmas from OpenAI's Apache-2.0
September 2026 source (https://github.com/openai/math, revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a). The relevant licenses are included.
No π-exponent or Catalan endpoint theorem is an assumption of this result.

REPRODUCTION

Install the pinned Lean toolchain with elan. Enter anc/lean, then run:

    lake exe cache get
    lake build Solution Zeta32Extension.Verification
    lake env lean Zeta32Extension/Verification.lean
    lake env lean --run VerifyZeta32Components.lean

Do not rebuild imported modules while the replay runs. Dependency and
toolchain retrieval require network access. The manifest pins transitive
dependencies. There are no absolute development-directory paths in this
package's build configuration, and no precompiled proof objects are included.

OBSERVED VERIFICATION

All 123 explicitly listed extension theorem declarations passed the
transitive axiom audit. Fresh Lean-kernel replay passed for 21 selected
roots and their closure of 82,674 declarations, including both endpoints.
Only propext, Classical.choice, Quot.sound were permitted. Unsafe, partial,
and nonstandard-axiom dependencies were rejected. Replay uses Lean's own
kernel, not an independently implemented proof checker.

The checked publication package was rebuilt in a fresh project while
reusing pinned dependency caches. This is not a clean-machine installation
or a full Mathlib rebuild. The source archive contains SHA-256 inventories;
the manuscript can be rebuilt from main.tex with latexmk. The public
README.txt gives file-integrity and TeX commands.
The numerical approximation threshold is not computed.
In the Zenodo release, RIGHTS.txt specifies the licenses for the manuscript
and new code; existing third-party source licenses and notices are retained.
