/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Inclusion
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.Continuous

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped MorphismOfTopoiIn

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable (S : Scheme.{u}) (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
variable (p : ℕ) [Fact (Nat.Prime p)]
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/-- The inclusion of the small crystalline site induces a geometric morphism from the
small crystalline topos to the big crystalline topos. -/
noncomputable def smallToBigCrystallineToposMorphism :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u + 1}
      (crystallineZariskiTopology S I γ h_compatible X x₀)
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) :=
  (smallCrystallineInclusion S I γ h_compatible X x₀).morphismOfTopoiInOfCocontinuous.{u + 1}
    (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
    (crystallineZariskiTopology S I γ h_compatible X x₀)

/-- Continuous sheaf pullback along the small crystalline inclusion preserves finite limits. -/
instance smallCrystallineInclusion_sheafPullback_preservesFiniteLimits :
    PreservesFiniteLimits
      ((smallCrystallineInclusion S I γ h_compatible X x₀).sheafPullback (Type (u + 1))
        (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
        (crystallineZariskiTopology S I γ h_compatible X x₀)) := sorry

/-- The continuous sheaf adjunction of the inclusion defines a geometric morphism from the
big crystalline topos to the small crystalline topos. -/
noncomputable def bigToSmallCrystallineToposMorphism :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u + 1}
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (crystallineZariskiTopology S I γ h_compatible X x₀) :=
  (smallCrystallineInclusion S I γ h_compatible X x₀).morphismOfTopoiInOfContinuous.{u + 1}
    (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
    (crystallineZariskiTopology S I γ h_compatible X x₀)

/-- The unit of the continuous sheaf adjunction of the small crystalline inclusion is
invertible. -/
instance smallCrystallineInclusion_sheafAdjunctionContinuous_unit_isIso :
    IsIso ((smallCrystallineInclusion S I γ h_compatible X x₀).sheafAdjunctionContinuous
      (Type (u + 1)) (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (crystallineZariskiTopology S I γ h_compatible X x₀)).unit := sorry

/-- The direct image of the big-to-small crystalline morphism is naturally isomorphic to the
inverse image of the inclusion-induced small-to-big morphism. -/
noncomputable def bigToSmallCrystallineToposMorphism_pushforwardIso :
    (bigToSmallCrystallineToposMorphism S I γ h_compatible X x₀ p s h_p).pushforward ≅
      (smallToBigCrystallineToposMorphism S I γ h_compatible X x₀ p s h_p).inverseImage :=
  (Functor.CocontinuousPullback.comparisonIso.{u + 1}
    (smallCrystallineInclusion S I γ h_compatible X x₀)
    (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
    (crystallineZariskiTopology S I γ h_compatible X x₀)).symm

/-- The inverse image of the composite of the big-to-small and small-to-big crystalline
morphisms is naturally isomorphic to the identity on the small crystalline topos. -/
noncomputable def bigToSmallCrystallineToposMorphism_comp_smallToBigInverseImageIso :
    (MorphismOfTopoiIn.comp
      (bigToSmallCrystallineToposMorphism S I γ h_compatible X x₀ p s h_p)
      (smallToBigCrystallineToposMorphism S I γ h_compatible X x₀ p s h_p)).inverseImage ≅
      (MorphismOfTopoiIn.id
        (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)).inverseImage :=
  Functor.isoWhiskerLeft
    ((smallCrystallineInclusion S I γ h_compatible X x₀).sheafPullback (Type (u + 1))
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (crystallineZariskiTopology S I γ h_compatible X x₀))
    (Functor.CocontinuousPullback.comparisonIso.{u + 1}
      (smallCrystallineInclusion S I γ h_compatible X x₀)
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (crystallineZariskiTopology S I γ h_compatible X x₀)) ≪≫
    (asIso ((smallCrystallineInclusion S I γ h_compatible X x₀).sheafAdjunctionContinuous
      (Type (u + 1)) (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (crystallineZariskiTopology S I γ h_compatible X x₀)).unit).symm

end AlgebraicGeometry.Scheme.Crystalline
