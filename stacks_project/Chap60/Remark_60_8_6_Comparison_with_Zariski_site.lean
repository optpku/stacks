/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.Definition_60_8_4
public import stacks_project.Chap60.Lemma_60_8_2
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.Big
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

/-- Remark 60.8.6 (Comparison with Zariski site) (1): in Situation 60.7.5,
the forgetful functor from the relative crystalline site to `Over X` is
cocontinuous for the crystalline and big Zariski topologies. -/
@[stacks 07ID]
instance crystallineForgetful_isCocontinuous {p : ℕ} [Fact (Nat.Prime p)]
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) :
    (crystallineForgetful S I γ h_compatible s X x₀ h_p).IsCocontinuous
      (crystallineZariskiTopology S I γ h_compatible X x₀)
      X.bigZariskiTopology := sorry

/-- Remark 60.8.6 (Comparison with Zariski site) (2): the cocontinuous
forgetful functor induces a morphism of topoi from the big crystalline topos
of `X/S` to the big Zariski topos of `X`. -/
@[stacks 07ID]
noncomputable def crystallineToposMorphism {p : ℕ} [Fact (Nat.Prime p)]
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
      (crystallineForgetful S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P] :
    MorphismOfTopoiIn X.bigZariskiTopology
      (crystallineZariskiTopology S I γ h_compatible X x₀) :=
  (crystallineForgetful S I γ h_compatible s X x₀ h_p).morphismOfTopoiInOfCocontinuous
    (crystallineZariskiTopology S I γ h_compatible X x₀) X.bigZariskiTopology

/-- The inverse-image functor of `crystallineToposMorphism` is the
sheafified pullback along the crystalline forgetful functor. -/
theorem crystallineToposMorphism_inverseImage {p : ℕ} [Fact (Nat.Prime p)]
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
      (crystallineForgetful S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P] :
    (crystallineToposMorphism S I γ h_compatible s X x₀ h_p).inverseImage =
      (crystallineForgetful S I γ h_compatible s X x₀ h_p).sheafPullbackCocontinuous
        (Type (u + 1))
        (crystallineZariskiTopology S I γ h_compatible X x₀)
        X.bigZariskiTopology := sorry

end AlgebraicGeometry.Scheme.Crystalline

end
