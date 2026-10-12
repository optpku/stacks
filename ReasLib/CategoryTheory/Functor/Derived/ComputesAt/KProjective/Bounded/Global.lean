/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Existence
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.KProjective.Bounded
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Global Bounded Left Derived Functors from Projective Resolutions

This leaf globalizes bounded-above K-projective computation without choosing a derived-category
model. Its primary criterion is an objectwise family of cochain-level projective resolutions.
Under enough projectives, the stronger source-definedness conclusion is registered globally; its
objectwise and pointwise consequences then follow from the canonical forgetful instances.
-/

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.KProjective.Bounded

variable {A : Type u₁} {D : Type u₂}
  [Category.{v₁} A] [Abelian A] [Category.{v₂} D]

/-- Objectwise projective resolutions make the
left-derived indexing diagrams of a functor out of `K⁻(A)` essentially constant everywhere. -/
@[stacks 05TI "formal projective dual, objectwise resolutions"]
theorem everywhereDefinedOfResolutions
    (T : HomotopyCategory.Minus A ⥤ D)
    (h_resolution : ∀ K : CochainComplex.Minus A,
      Nonempty (CochainComplex.ProjectiveResolution K.obj)) :
    LeftDerived.EverywhereDefined T (HomotopyCategory.Minus.quasiIso A) := sorry

/-- The objectwise projective-resolution criterion supplies a pointwise left-derived functor at
bounded-above quasi-isomorphisms. -/
@[stacks 05TI "formal projective dual, objectwise resolutions"]
theorem hasPointwiseOfResolutions
    (T : HomotopyCategory.Minus A ⥤ D)
    (h_resolution : ∀ K : CochainComplex.Minus A,
      Nonempty (CochainComplex.ProjectiveResolution K.obj)) :
    T.HasPointwiseLeftDerivedFunctor (HomotopyCategory.Minus.quasiIso A) := by
  classical
  intro object
  obtain ⟨resolution⟩ := h_resolution ⟨object.obj.as, object.property⟩
  let model : HomotopyCategory.Minus A :=
    ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj resolution.complex,
      resolution.minus⟩
  have modelKProjective : CochainComplex.IsKProjective model.obj.as := by
    change CochainComplex.IsKProjective resolution.complex
    infer_instance
  let comparison : model ⟶ object := ObjectProperty.homMk
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map resolution.π)
  have comparisonMem : HomotopyCategory.Minus.quasiIso A comparison :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff resolution.π).mpr resolution.quasiIso
  apply (T.hasPointwiseLeftDerivedFunctorAt_iff_of_mem
    (HomotopyCategory.Minus.quasiIso A) comparison comparisonMem).mp
  constructor
  let localization := MorphismProperty.Q (HomotopyCategory.Minus.quasiIso A)
  let initialProof : Limits.IsInitial
      (StructuredArrow.mk (𝟙 (localization.obj model))) :=
    { desc := fun cocone => StructuredArrow.homMk
        ((Localization.map_bijective model cocone.pt.right).surjective
          cocone.pt.hom).choose
        (by
          change 𝟙 _ ≫ localization.map _ = _
          simpa only [Category.id_comp] using
            ((Localization.map_bijective model cocone.pt.right).surjective
              cocone.pt.hom).choose_spec)
      uniq := by
        intro cocone morphism condition
        apply CommaMorphism.ext
        · simp
        · apply (Localization.map_bijective model cocone.pt.right).injective
          have equality := StructuredArrow.w morphism
          change 𝟙 _ ≫ localization.map morphism.right = cocone.pt.hom at equality
          have mapEquality : localization.map morphism.right = cocone.pt.hom := by
            simpa only [Category.id_comp] using equality
          exact mapEquality.trans
            ((Localization.map_bijective model cocone.pt.right).surjective
              cocone.pt.hom).choose_spec.symm }
  exact Limits.HasLimit.mk
    { cone := _, isLimit := Limits.limitOfDiagramInitial initialProof _ }

/-- Enough projectives make the left-derived indexing
diagram of every functor out of `K⁻(A)` essentially constant at every source object. -/
@[stacks 05TI "formal projective dual, enough projectives"]
instance everywhereDefinedOfEnoughProjectives
    [EnoughProjectives A] (T : HomotopyCategory.Minus A ⥤ D) :
    LeftDerived.EverywhereDefined T (HomotopyCategory.Minus.quasiIso A) := sorry

/-- Objectwise projective resolutions make the left-derived indexing diagram essentially
constant at each bounded-above homotopy object. -/
@[stacks 05TI "formal projective dual, source-definedness"]
theorem definedAtOfResolutions
    (T : HomotopyCategory.Minus A ⥤ D)
    (h_resolution : ∀ K : CochainComplex.Minus A,
      Nonempty (CochainComplex.ProjectiveResolution K.obj))
    (X : HomotopyCategory.Minus A) :
    LeftDerived.DefinedAt T (HomotopyCategory.Minus.quasiIso A) X := sorry

end CategoryTheory.Functor.KProjective.Bounded
