/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import stacks_project.Chap61.Lemma_61_26_5_ShortComplex
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
variable [QuasiCompact (closedImmersionComplement i).ι]
variable [∀ F : (closedImmersionComplement i).toScheme.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (restriction (closedImmersionComplement i).ι).op.HasLeftKanExtension F]
variable [∀ G : X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (smallProetalePullback i).op.HasLeftKanExtension G]
variable [HasWeakSheafify (topology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (topology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (topology Z) AddCommGrpCat.{u + 1}]
variable [HasZeroMorphisms (Sheaf (topology X) AddCommGrpCat.{u + 1})]
variable (F : Sheaf (topology X) AddCommGrpCat.{u + 1})

/-- Lemma 61.26.5: if `i : Z ⟶ X` is a closed immersion and
`j = (closedImmersionComplement i).ι` is the quasi-compact open complement
inclusion, then for every abelian sheaf `F` on `X_proétale` the canonical
sequence `0 ⟶ j_! (j⁻¹ F) ⟶ F ⟶ i_* (i⁻¹ F) ⟶ 0` is short exact, where all
functors are the small pro-étale functors `abelianExtensionByZero`,
`restrictionSheaf`, `smallPushforward`, and `smallInverseImage`. -/
@[stacks 09AH]
theorem abelianClosedOpenShortComplex_shortExact :
    (abelianClosedOpenShortComplex i F).ShortExact := sorry

end AlgebraicGeometry.Scheme.ProEt
