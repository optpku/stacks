module

public import stacks_project.Chap60.Remark_60_8_7_Structure_morphism_Functor
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

/-- Remark 60.8.7 (Structure morphism): the cocontinuous morphism of topoi from the
big crystalline site of `X/S` to the big Zariski topos of `S`. -/
@[stacks 07IE]
noncomputable def bigStructureMorphism {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    [HasSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀)
      (Type (u + 1))]
    [∀ P : (RelativeCRIS S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (bigStructureFunctor S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P] :
    MorphismOfTopoiIn S.bigZariskiTopology
      (crystallineZariskiTopology S I γ h_compatible X x₀) :=
  (bigStructureFunctor S I γ h_compatible s X x₀ h_p).morphismOfTopoiInOfCocontinuous
    (crystallineZariskiTopology S I γ h_compatible X x₀) S.bigZariskiTopology

/-- The direct-image functor of `bigStructureMorphism` is the cocontinuous sheaf pushforward. -/
theorem bigStructureMorphism_pushforward {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    [HasSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀)
      (Type (u + 1))]
    [∀ P : (RelativeCRIS S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (bigStructureFunctor S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P] :
    (bigStructureMorphism S I γ h_compatible s X x₀ h_p).pushforward =
      (bigStructureFunctor S I γ h_compatible s X x₀ h_p).sheafPushforwardCocontinuous
        (Type (u + 1))
        (crystallineZariskiTopology S I γ h_compatible X x₀)
        S.bigZariskiTopology := sorry

/-- The inverse-image functor of `bigStructureMorphism` is the sheafified cocontinuous pullback. -/
theorem bigStructureMorphism_inverseImage {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    [HasSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀)
      (Type (u + 1))]
    [∀ P : (RelativeCRIS S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (bigStructureFunctor S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P] :
    (bigStructureMorphism S I γ h_compatible s X x₀ h_p).inverseImage =
      (bigStructureFunctor S I γ h_compatible s X x₀ h_p).sheafPullbackCocontinuous
        (Type (u + 1))
        (crystallineZariskiTopology S I γ h_compatible X x₀)
        S.bigZariskiTopology := sorry

end AlgebraicGeometry.Scheme.Crystalline

end
