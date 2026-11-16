# Palomar module-source collision repair

## Reported failure

The maintainer submitted commit
`186c74eee4e960e1d0b6621e0e9310156d91bbe2` of this repository. The actual
[Palomar mechanical run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/43906636480)
returned diagnostic `challenge.module_root_shadowed`.

The configured module was the top-level `Challenge`. The pinned
`large_indecomposable` dependency also contains a top-level `Challenge.lean`.
Palomar's report resolved the source path to
`.lake/packages/large_indecomposable/Challenge.lean`, not this repository's
107-line source. This is a module-source/provenance ambiguity. The report did
not reach independent proof replay (`kernels` is empty); it is not a new
mathematical counterexample or an axiom failure.

The earlier project CI checks successfully built and compared the intended
project modules, but did not test this additional Palomar/Verso source-resolution
requirement. Passing those checks is not equivalent to passing the complete
registry pipeline. This repair addresses the reported repository-side issue.

## Changes

* Move the exact local Challenge to `C3PalomarSubmission/Challenge.lean`.
* Move the exact local Solution to `C3PalomarSubmission/Solution.lean`, avoiding
  the analogous root `Solution.lean` name in the dependency as well.
* Configure `C3PalomarSubmission.Challenge` and `C3PalomarSubmission.Solution`
  in `comparator.json`; keep `PalomarC3.main_result` as the compared declaration.
* Give the two modules separate Lake library targets. The default target
  contains only Solution, so it does not build or export the deliberate
  Challenge hole as a proved result.
* Update audit imports, CI build targets, metadata, reader-facing references,
  source checksum paths and the provenance inventory.
* Make the integrity script derive paths from the configured dotted module
  names and reject a registry module's top-level name if any pinned dependency
  contains that file or directory.

The chosen top-level directory `C3PalomarSubmission` is absent from all pinned
Git dependencies, checked at their actual locally resolved revisions.
The moved source files are byte-identical to their original contents. The
mathematical namespace, theorem type, definitions, proof body, standard axiom
policy, toolchain and dependency revisions are unchanged.

## Regression and validation

`python3 scripts/test_module_layout.py` runs a disposable source-only regression
copy. It accepts the new layout, rejects both an artificial directory and a
Lean-file entry with the configured top-level name under a dependency root,
and rejects an unavailable dependency instead of silently skipping it. Both
CI workflows run this regression alongside the real dependency-root audit.
The integrity check also checks
Challenge definition identity, complete checksums/provenance inventory, and
absence of the configured Challenge module from Solution's import closure.
The new modules are rebuilt, their precise theorem types and axiom closures
are checked, and both hosted CI workflows run on the repaired commit.

These checks address this reported conflict and revalidate the proof; they do
not claim a successful new Palomar submission. The maintainer must resubmit
with the repaired commit's full 40-character SHA. The selected project remains
the repository root, with `comparator.json` and `formalization.yaml` at their
standard locations. The module paths are controlled by the JSON configuration,
not by a new project-path input.
