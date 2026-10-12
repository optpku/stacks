/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import stacks_project.Chap61.Lemma_61_19_1_Comparison
public import stacks_project.Chap61.Remark_61_14_4_Sections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.19.4

On an affine scheme, the pro-étale cohomology of `ε⁻¹ I` vanishes in positive
degrees when `I` is an injective abelian sheaf on the small étale site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsAffine X]
variable [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}, (etaleToProEt X).op.HasLeftKanExtension F]
variable [HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u}]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify (ProEt.topology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (ProEt.topology X) AddCommGrpCat.{u})]

/-- Lemma 61.19.4: if `X` is an affine scheme and `I` is an injective abelian sheaf
on `X.Etale`, then `H^p(X.ProEt, ε⁻¹ I) = 0` for all `p > 0`. -/
@[stacks 099U]
theorem etaleToProEtPullback_injective_isZero_cohomology
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) [Injective I]
    {p : ℕ} (hp : 0 < p) :
    IsZero (((etaleToProEtPullback X AddCommGrpCat.{u}).obj I).H' p (ProEt.globalProEt X)) :=
  sorry

end AlgebraicGeometry.Scheme
