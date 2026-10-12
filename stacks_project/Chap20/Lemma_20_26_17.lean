/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.KFlat.Factorization
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory HomologicalComplex

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/- Domain-style sampling for Lemma 20.26.17:
- primary domain: factorization up to homotopy of morphisms of cochain complexes of
  `𝒪_X`-modules through quasi-isomorphisms with K-flat source;
- sampled owner declarations:
  `SheafOfModules.RingedSite.exists_homotopy_factorization_through_kFlat_quasiIso`,
  `SheafOfModules.RingedSite.exists_termwiseFlat_homotopy_factorization_through_kFlat_quasiIso`,
  `CochainComplex.IsKFlat`,
  `CochainComplex.IsTermwiseFlat`,
  `CochainComplex.isTermwiseFlat_iff`,
  `Homotopy`, and `QuasiIso`;
- best owner abstraction: the ringed-site theorems from Chapter `21` are the canonical core
  owners, while this file should expose only the opens-site specialization to a ringed space and
  the bridge from the canonical ringed-space owner `IsTermwiseFlat K` to the source wording that
  each term `K.X n` is flat;
- primitive vs derived: primitive data are the intermediate complex `N` and the comparison maps
  `b`, `c`; the homotopy, K-flatness, quasi-isomorphism, and termwise-flatness clauses remain on
  their canonical owners.

Source/core/bridge triage:
- `source-facing`: the ringed-space factorization statement and its flat-terms refinement;
- `core/canonical`: the Chapter `21` ringed-site factorization theorems together with
  `K.IsKFlat`, `IsTermwiseFlat K`, `Homotopy a (b ≫ c)`, and `QuasiIso c`;
- `bridge/view`: specialization from the opens ringed site of `X` to `RingedSpace.Modules X`, and
  the translation between `IsTermwiseFlat` and degreewise flatness via
  `CochainComplex.isTermwiseFlat_iff`. -/

/- Lemma 20.26.17 (0G6V): the ringed-space factorization is owned by the shared `CochainComplex`
API, with termwise-flat and degreewise-flat companions. -/
@[stacks 0G6V]
#check @AlgebraicGeometry.RingedSpace.CochainComplex.exists_homotopy_factorization_through_kFlat_quasiIso

#check @AlgebraicGeometry.RingedSpace.CochainComplex.exists_termwiseFlat_homotopy_factorization_through_kFlat_quasiIso

#check @AlgebraicGeometry.RingedSpace.CochainComplex.exists_homotopy_factorization_through_kFlat_quasiIso_of_termwiseFlat
#check @AlgebraicGeometry.RingedSpace.CochainComplex.isTermwiseFlat_iff

end AlgebraicGeometry.RingedSpace
