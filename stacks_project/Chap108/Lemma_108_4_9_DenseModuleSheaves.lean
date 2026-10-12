/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap108.Lemma_108_4_9_ModuleSheaves
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site

variable {C : Type v} [Category.{u} C] (J : GrothendieckTopology C)
  (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Testing maps from a free representable sheaf tests every section at that object. -/
theorem app_eq_of_freeAt {M N : SheafOfModules.{u} R} (f g : M ⟶ N) (X : C)
    (h : ∀ b : freeAt J R X ⟶ M, b ≫ f = b ≫ g) :
    f.val.app (op X) = g.val.app (op X) := by
  ext x
  let a := (PresheafOfModules.freeYonedaEquiv
    (M := (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).obj M)
    (X := X)).symm x
  let b := ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ M).symm a
  have eq := congrArg
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ N)
    (h b)
  have eq' :=
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_right b f).symm.trans
      (eq.trans ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_right b g))
  have values := congrArg PresheafOfModules.freeYonedaEquiv eq'
  simpa only [b, Equiv.apply_symm_apply, PresheafOfModules.freeYonedaEquiv_comp, a,
    Equiv.apply_symm_apply] using! values

variable {D : Type u} [Category.{u} D] (K : GrothendieckTopology D) (F : D ⥤ C)
  [F.IsContinuous K J]
  [(F.sheafPushforwardContinuous AddCommGrpCat.{u} K J).Faithful]

include K F in
/-- A small family detecting sheaf sections supplies a small generating family of modules. -/
theorem denseFreeAtSeparating :
    ObjectProperty.IsSeparating (.ofObj (fun d : D ↦ freeAt J R (F.obj d))) := by
  intro M N f g h
  apply (SheafOfModules.toSheaf R).map_injective
  apply (F.sheafPushforwardContinuous AddCommGrpCat.{u} K J).map_injective
  ext ⟨d⟩ x
  exact ConcreteCategory.congr_hom
    (app_eq_of_freeAt J R f g (F.obj d)
      (fun b ↦ h _ (ObjectProperty.ofObj_apply _ d) b)) x

/-- A specified generator in the original module category, without any universe unlift. -/
noncomputable def denseGenerator : SheafOfModules.{u} R :=
  ∐ (fun d : D ↦ freeAt J R (F.obj d))

include K F in
/-- The specified dense-site generator separates module morphisms. -/
theorem denseGeneratorSeparates : IsSeparator (denseGenerator J R F) :=
  (denseFreeAtSeparating J R K F).isSeparator_coproduct

include K F in
/-- A dense small family certifies the original module category as Grothendieck. -/
theorem denseModulesGrothendieck [LocallySmall.{u} (Sheaf J AddCommGrpCat.{u})] :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) := by
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := sheafAB5 J R
  exact {
    locallySmall := locallySmall_of_faithful (SheafOfModules.toSheaf R)
    hasSeparator := ⟨denseGenerator J R F, denseGeneratorSeparates J R K F⟩ }

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site
