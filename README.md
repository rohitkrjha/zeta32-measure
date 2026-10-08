# An explicit irrationality-exponent bound for ζ(3) − rζ(2)

Rohit Kumar Jha

[Read the paper](release/zeta32-measure-v2.pdf) · [Version v2](https://github.com/rohitkrjha/zeta32-measure/releases/tag/v2) · [LaTeX source](sources/main.tex) · [Lean project](sources/anc/lean)

## Version v2

This revision removes the subtitle, expands the rational matrix definitions and energy estimates, and reorganizes the proof and supporting documentation. The theorem statements and mathematical Lean sources are unchanged. The original [v1 release](https://github.com/rohitkrjha/zeta32-measure/releases/tag/v1) is preserved.

## Result

For each fixed rational number r,

$$
2\leq\mu\bigl(\zeta(3)-r\zeta(2)\bigr)\leq 10{,}000.
$$

The approximation threshold may depend on r. This is not a simultaneous
bound with arbitrarily varying coefficients. The exponent is not optimized;
the special case r = 0 has stronger classical bounds.

The manuscript gives the full statements, hypotheses, proofs, and references.

## Contents

- **release/** contains the manuscript PDF and the four companion files prepared for the matching Zenodo deposit.
- **sources/** is the exact unpacked contents of the source archive, including its original checksum inventories.
- **sources/anc/lean/** contains the formalization, pinned Lake manifest, verification scripts, and required upstream source files.
- **CITATION.cff** supplies citation metadata for the paper and its source repository.
- **scripts/check_integrity.py** checks the release files and their agreement with the unpacked sources.

The source archive is intentionally included alongside the browsable source tree so that the downloadable publication package can be checked against it.

## Reproduce

First check the distributed files from the repository root:

    python3 scripts/check_integrity.py

To compile the manuscript, install a TeX distribution and latexmk, then run:

    cd sources
    latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

To check the proof, install [elan](https://github.com/leanprover/elan), then run the following from the repository root. The checked-in lean-toolchain and lake-manifest.json select the required versions.

    cd sources/anc/lean
    lake exe cache get
    lake build Solution Zeta32Extension.Verification
    lake env lean --run VerifyZeta32Components.lean

Run these commands sequentially. Downloads require network access. Do not rebuild imported modules while the kernel replay is running. Compiled Lean objects and dependency caches are not included.

The pinned versions and source provenance are documented in [the ancillary README](sources/anc/README.txt). The original package instructions are also available in [release/README.txt](release/README.txt).

## Verification

The v2 checks passed the Lean build, a transitive axiom audit of 123 extension theorems, and a fresh-environment Lean-kernel replay of 21 selected roots and their closure of 82,674 declarations. Only propext, Classical.choice, and Quot.sound were permitted. The replay includes the denominator theorem and the irrationality-exponent corollary; the final direct determinant proof does not assume the earlier all-minors hypothesis.

These checks reused pinned dependency/build caches; they were not clean-machine installations or full Mathlib source rebuilds. The replay uses Lean's own kernel.

The GitHub Actions workflow checks publication-file integrity only. It does not replace the Lean commands above or claim a new proof replay on every commit.

## Citation and versions

Use the repository's **Cite this repository** control or [CITATION.cff](CITATION.cff). Version v2 identifies the manuscript and source package in this release. A Zenodo DOI will be added once the corresponding record has been reserved or published; no DOI is claimed here.

Substantive changes to the manuscript or proof will receive a new release rather than changing the v2 tag. Later citation-only metadata updates may appear on the main branch without changing the v2 mathematical sources.

## Provenance and licenses

The construction is a quantitative extension of Qian Tang's qualitative irrationality proof, which builds on Fauzan's determinant method. Source-file notices identify further adapted results. The upstream NOTICE and license files are retained in sources/anc/lean.

The manuscript, LaTeX/bibliography sources, and accompanying documentation are licensed under **CC BY 4.0**. Original Lean code, verification scripts, and build configuration are licensed under **Apache 2.0**. Third-party code retains its existing licenses and notices. These licenses apply to different components, not as interchangeable alternatives for every file.

See [LICENSE](LICENSE), [the package rights notice](sources/RIGHTS.txt), and the upstream notices retained under sources/anc/lean. The bibliography credits the mathematical sources.
