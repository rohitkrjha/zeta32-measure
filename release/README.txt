An explicit irrationality-exponent bound for ζ(3) − rζ(2): A Lean-verified quantitative extension
====================================================

Author: Rohit Kumar Jha
Version: v1

FILES

  zeta32-measure-v1.pdf
      The research manuscript.

  zeta32-measure-v1-sources.zip
      LaTeX manuscript sources and the supporting Lean source project.
      Extract into an empty directory. The manuscript is main.tex; the
      formalization is in anc/lean. See anc/README.txt for source provenance,
      dependency revisions, and the verification procedure.

  README.txt
      This file: contents, reproduction commands, and integrity checks.

  RIGHTS.txt
      Licensing scope for the manuscript, new code, and third-party code.
      An identical copy is included in the source archive.

  SHA256SUMS.txt
      SHA-256 digests of the other four deposited files. The checksum file
      does not list itself.

REBUILD THE MANUSCRIPT

From the extracted source directory, with a TeX distribution and latexmk:

  latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

The bibliography is included in main.tex.

CHECK THE FORMALIZATION

Install the Lean toolchain specified in anc/lean/lean-toolchain using elan.
From the extracted source directory:

  cd anc/lean
  lake exe cache get
  lake build Solution Zeta32Extension.Verification
  lake env lean --run VerifyZeta32Components.lean

Run these commands sequentially. Toolchain and dependency downloads require
network access. Compiled Lean objects and dependency caches are not included.
Do not rebuild imported modules while the final replay is running.

The verification target audits 123 extension theorems. The replay rechecks
21 selected roots and their closure of 82,674 declarations using Lean's own
kernel, allowing only propext, Classical.choice, and Quot.sound.

CHECK FILE INTEGRITY

From the directory containing the five deposited files, on macOS:

  shasum -a 256 -c SHA256SUMS.txt

On Linux, the corresponding command is:

  sha256sum -c SHA256SUMS.txt

The source archive also includes SHA256SUMS.txt for its other members and
anc/SHA256SUMS for the ancillary source files. After extraction, the same
checksum command can be used at the archive root; for the ancillary
inventory, run it from anc with SHA256SUMS instead of SHA256SUMS.txt.

PROVENANCE AND RIGHTS

The construction is a quantitative extension of Qian Tang's qualitative
irrationality proof, which builds on Fauzan's determinant method. Source-
file notices identify further adapted results. The upstream NOTICE and
license files are retained in anc/lean. Bundled upstream files and their license
notices are retained. The source archive includes the formalization,
supporting local mathematical sources, build configuration, verification
scripts, and licenses.

See RIGHTS.txt for the applicable licensing scope.
