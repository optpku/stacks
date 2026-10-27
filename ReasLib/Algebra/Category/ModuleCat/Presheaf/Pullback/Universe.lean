/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.GrothendieckUniverse

/-!
# Pullback of module presheaves in a bounded section universe

Free represented modules and their cokernel presentations construct left adjoints
without identifying the coefficient, section, or indexing universes.
-/

@[expose] public section

open CategoryTheory Limits Opposite Functor

noncomputable section

universe uC vC uD vD r w

namespace PresheafOfModules.UniversePullback

section Presentation

variable {C : Type uC} [Category.{vC} C] {R : Cᵒᵖ ⥤ RingCat.{r}}
  [UnivLE.{uC, w}] [UnivLE.{max vC r, w}]

/-- Sections indexed by source objects form a small type in the section universe. -/
private instance smallElements (M : PresheafOfModules.{w} R) : Small.{w} M.Elements := by
  change Small.{w} (Σ X : Cᵒᵖ, M.obj X)
  infer_instance

/-- The free represented module indexed by a section's underlying object. -/
private abbrev generator {M : PresheafOfModules.{w} R} (m : M.Elements) :=
  freeRepresentableOfUnivLE R m.1.unop

/-- The free represented morphism determined by a section. -/
private abbrev generatorMap {M : PresheafOfModules.{w} R} (m : M.Elements) :
    generator.{uC, vC, r, w} m ⟶ M := freeRepresentableOfUnivLEEquiv R |>.symm m.2

/-- The coproduct of free represented modules indexed by all sections. -/
private abbrev generators (M : PresheafOfModules.{w} R) : PresheafOfModules.{w} R :=
  ∐ (generator.{uC, vC, r, w} (M := M))

/-- The evaluation morphism sends each free generator to its indexing section. -/
private def evaluationMap (M : PresheafOfModules.{w} R) : generators.{uC, vC, r, w} M ⟶ M :=
  Sigma.desc generatorMap.{uC, vC, r, w}

/-- The section of the free coproduct determined by its corresponding summand. -/
private def generatorSection {M : PresheafOfModules.{w} R} (m : M.Elements) :
    (generators.{uC, vC, r, w} M).obj m.1 :=
  freeRepresentableOfUnivLEEquiv R (Sigma.ι (generator.{uC, vC, r, w} (M := M)) m)

/-- Evaluation recovers the section indexing a free generator. -/
private lemma evaluationMap_generatorSection {M : PresheafOfModules.{w} R}
    (m : M.Elements) :
    (evaluationMap.{uC, vC, r, w} M).app _ (generatorSection.{uC, vC, r, w} m) = m.2 := by
  have h : Sigma.ι (generator.{uC, vC, r, w} (M := M)) m ≫
      evaluationMap.{uC, vC, r, w} M = generatorMap.{uC, vC, r, w} m :=
    Sigma.ι_desc _ m
  have he := freeRepresentableOfUnivLEEquiv_comp R
    (Sigma.ι (generator.{uC, vC, r, w} (M := M)) m) (evaluationMap.{uC, vC, r, w} M)
  exact he.symm.trans ((congrArg (freeRepresentableOfUnivLEEquiv R) h).trans
    ((freeRepresentableOfUnivLEEquiv R).apply_symm_apply m.2))

/-- Every section is in the image of the free evaluation morphism. -/
private instance evaluationMap_epi (M : PresheafOfModules.{w} R) :
    Epi (evaluationMap.{uC, vC, r, w} M) :=
  epi_of_surjective (fun X m ↦ ⟨generatorSection.{uC, vC, r, w} (M.elementsMk X m),
    evaluationMap_generatorSection.{uC, vC, r, w} (M.elementsMk X m)⟩)

/-- Free generators of the evaluation kernel give the relations morphism. -/
private def relations (M : PresheafOfModules.{w} R) :
    generators.{uC, vC, r, w} (kernel (evaluationMap.{uC, vC, r, w} M)) ⟶ generators.{uC, vC, r, w} M :=
  evaluationMap.{uC, vC, r, w} (kernel (evaluationMap.{uC, vC, r, w} M)) ≫ kernel.ι _

/-- The relations vanish after evaluation. -/
private lemma relations_evaluationMap (M : PresheafOfModules.{w} R) :
    relations.{uC, vC, r, w} M ≫ evaluationMap.{uC, vC, r, w} M = 0 := by
  simp [relations]

/-- A module presheaf is the vertex of its free-presentation cokernel cofork. -/
private abbrev presentation (M : PresheafOfModules.{w} R) :
    CokernelCofork (relations.{uC, vC, r, w} M) :=
  CokernelCofork.ofπ _ (relations_evaluationMap.{uC, vC, r, w} M)

/-- Evaluation is the cokernel of the free relations morphism. -/
private def presentationIsColimit (M : PresheafOfModules.{w} R) :
    IsColimit (presentation.{uC, vC, r, w} M) := by
  let S := ShortComplex.mk _ _ (relations_evaluationMap.{uC, vC, r, w} M)
  let T := ShortComplex.mk _ _ (kernel.condition (evaluationMap.{uC, vC, r, w} M))
  let φ : S ⟶ T :=
    { τ₁ := evaluationMap.{uC, vC, r, w} _
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  exact ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
    (T.exact_of_f_is_kernel (kernelIsKernel _))).gIsCokernel

end Presentation

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{r}} {S : Cᵒᵖ ⥤ RingCat.{r}}
  [UnivLE.{uC, w}] [UnivLE.{max vC r, w}] [UnivLE.{max vD r, w}]
  (φ : S ⟶ F.op ⋙ R)

/-- The target free represented module corepresents pushforward evaluated on a
source free represented module. -/
def freeCorepresentable (X : C) :
    (pushforward.{w} φ ⋙
      coyoneda.obj (op (freeRepresentableOfUnivLE S X))).CorepresentableBy
        (freeRepresentableOfUnivLE R (F.obj X)) where
  homEquiv {M} := (freeRepresentableOfUnivLEEquiv R).trans
    (freeRepresentableOfUnivLEEquiv S (M := (pushforward φ).obj M)).symm
  homEquiv_comp {M N} g f := (freeRepresentableOfUnivLEEquiv S).injective (by
    dsimp
    erw [Equiv.apply_symm_apply, freeRepresentableOfUnivLEEquiv_comp R]
    conv_rhs => erw [freeRepresentableOfUnivLEEquiv_comp S]
    erw [Equiv.apply_symm_apply]
    rfl)

/-- The partial pullback is defined on every free represented module. -/
private lemma pullbackObjIsDefined_free (X : C) :
    pullbackObjIsDefined.{w} φ (freeRepresentableOfUnivLE S X) :=
  (freeCorepresentable φ X).isCorepresentable

/-- Free cokernel presentations define the partial pullback on all module presheaves. -/
private lemma pullbackObjIsDefined_eq_top :
    pullbackObjIsDefined.{w} φ = ⊤ := by
  ext M
  simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
  apply leftAdjointObjIsDefined_of_isColimit (presentationIsColimit.{uC, vC, r, w} M)
  rintro (_ | _)
  all_goals
    apply leftAdjointObjIsDefined_colimit _
      (fun _ ↦ pullbackObjIsDefined_free φ _)

/-- Pushforward of module presheaves has a left adjoint when source objects,
both arrow universes, and coefficients fit in the section universe. -/
instance isRightAdjoint : (pushforward.{w} φ).IsRightAdjoint :=
  isRightAdjoint_of_leftAdjointObjIsDefined_eq_top (pullbackObjIsDefined_eq_top φ)

end PresheafOfModules.UniversePullback
