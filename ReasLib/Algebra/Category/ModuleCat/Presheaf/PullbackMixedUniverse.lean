module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback

/-!
# Pullback of module presheaves with independent indexing universes

Lifted free representables give presentations of module presheaves and hence
left adjoints to pushforward without requiring the indexing categories to be small.
-/

@[expose] public section

open CategoryTheory Limits Opposite Functor

noncomputable section

universe u v

namespace PresheafOfModules.MixedUniversePullback

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{max u v}}

/-- The free module presheaf on the lifted presheaf represented by an object. -/
def freeRepresentable (R : Cᵒᵖ ⥤ RingCat.{max u v}) (X : C) :
    PresheafOfModules.{max u v} R :=
  (free R).obj (uliftYoneda.{u}.obj X)

/-- Morphisms from a free representable module presheaf correspond to sections. -/
def freeHomEquiv {M : PresheafOfModules.{max u v} R} {X : C} :
    (freeRepresentable R X ⟶ M) ≃ M.obj (op X) :=
  PresheafOfModules.freeHomEquiv.trans uliftYonedaEquiv.{u}

/-- Evaluation on the lifted identity generator commutes with postcomposition. -/
theorem freeHomEquiv_comp {M N : PresheafOfModules.{max u v} R} {X : C}
    (m : freeRepresentable R X ⟶ M) (φ : M ⟶ N) :
    freeHomEquiv (m ≫ φ) = φ.app _ (freeHomEquiv m) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The morphism corresponding to a section takes the lifted identity generator to it. -/
theorem freeHomEquiv_symm_app (M : PresheafOfModules.{max u v} R) (X : C)
    (x : M.obj (op X)) :
    (freeHomEquiv.symm x).app (op X) (ModuleCat.freeMk (ULift.up (𝟙 X))) = x := by
  exact freeHomEquiv.apply_symm_apply x

private abbrev generator {M : PresheafOfModules.{max u v} R} (m : M.Elements) :=
  freeRepresentable R m.1.unop

private abbrev generatorMap {M : PresheafOfModules.{max u v} R} (m : M.Elements) :
    generator m ⟶ M := freeHomEquiv.symm m.2

private abbrev generators (M : PresheafOfModules.{max u v} R) :=
  ∐ (generator (M := M))

private def evaluationMap (M : PresheafOfModules.{max u v} R) : generators M ⟶ M :=
  Sigma.desc generatorMap

private def generatorSection {M : PresheafOfModules.{max u v} R} (m : M.Elements) :
    (generators M).obj m.1 :=
  (Sigma.ι (generator (M := M)) m).app _ (ModuleCat.freeMk (ULift.up (𝟙 _)))

private lemma evaluationMap_generatorSection {M : PresheafOfModules.{max u v} R}
    (m : M.Elements) :
    (evaluationMap M).app _ (generatorSection m) = m.2 := by
  have h := ConcreteCategory.congr_hom
    ((evaluation R m.1 ⋙ forget _).congr_map
      (Sigma.ι_desc (generatorMap (M := M)) m)) (ModuleCat.freeMk (ULift.up (𝟙 _)))
  exact h.trans (freeHomEquiv_symm_app M m.1.unop m.2)

private instance evaluationMap_epi (M : PresheafOfModules.{max u v} R) :
    Epi (evaluationMap M) :=
  epi_of_surjective (fun X m ↦ ⟨generatorSection (M.elementsMk X m),
    evaluationMap_generatorSection (M.elementsMk X m)⟩)

private def relations (M : PresheafOfModules.{max u v} R) :
    generators (kernel (evaluationMap M)) ⟶ generators M :=
  evaluationMap (kernel (evaluationMap M)) ≫ kernel.ι _

private lemma relations_evaluationMap (M : PresheafOfModules.{max u v} R) :
    relations M ≫ evaluationMap M = 0 := by
  simp [relations]

private abbrev presentation (M : PresheafOfModules.{max u v} R) :
    CokernelCofork (relations M) :=
  CokernelCofork.ofπ _ (relations_evaluationMap M)

private def presentationIsColimit (M : PresheafOfModules.{max u v} R) :
    IsColimit (presentation M) := by
  let S := ShortComplex.mk _ _ (relations_evaluationMap M)
  let T := ShortComplex.mk _ _ (kernel.condition (evaluationMap M))
  let φ : S ⟶ T :=
    { τ₁ := evaluationMap _
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  exact ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
    (T.exact_of_f_is_kernel (kernelIsKernel _))).gIsCokernel

variable {D : Type u} [Category.{v} D] {F : C ⥤ D}
  {R : Dᵒᵖ ⥤ RingCat.{max u v}} {S : Cᵒᵖ ⥤ RingCat.{max u v}}
  (φ : S ⟶ F.op ⋙ R)

private def freeCorepresentable (X : C) :
    (pushforward φ ⋙ coyoneda.obj (op (freeRepresentable S X))).CorepresentableBy
      (freeRepresentable R (F.obj X)) where
  homEquiv {M} := freeHomEquiv.trans
    (freeHomEquiv (M := (pushforward φ).obj M)).symm
  homEquiv_comp {M N} g f := freeHomEquiv.injective (by
    dsimp
    erw [Equiv.apply_symm_apply, freeHomEquiv_comp]
    conv_rhs => erw [freeHomEquiv_comp]
    erw [Equiv.apply_symm_apply]
    rfl)

private lemma pullbackObjIsDefined_free (X : C) :
    pullbackObjIsDefined φ (freeRepresentable S X) :=
  (freeCorepresentable φ X).isCorepresentable

private lemma pullbackObjIsDefined_eq_top :
    pullbackObjIsDefined.{max u v} φ = ⊤ := by
  ext M
  simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
  apply leftAdjointObjIsDefined_of_isColimit (presentationIsColimit M)
  rintro (_ | _)
  all_goals
    apply leftAdjointObjIsDefined_colimit _
      (fun _ ↦ pullbackObjIsDefined_free φ _)

/-- Pushforward of module presheaves has a left adjoint when coefficients contain
both the object and morphism universes of the indexing categories. -/
instance isRightAdjoint : (pushforward.{max u v} φ).IsRightAdjoint :=
  isRightAdjoint_of_leftAdjointObjIsDefined_eq_top (pullbackObjIsDefined_eq_top φ)

end PresheafOfModules.MixedUniversePullback
