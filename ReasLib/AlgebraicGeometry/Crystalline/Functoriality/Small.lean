/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Functoriality
public import ReasLib.AlgebraicGeometry.Crystalline.Topos

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Crystalline
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry

section Functoriality

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {S S' : Scheme.{u}} (I : S.IdealSheafData) (I' : S'.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (γ' : ∀ V : S'.affineOpens, DividedPowers (I'.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (h'_compatible :
  ∀ (V : S'.affineOpens) (f : Γ(S', V)),
    (γ' V).IsDPMorphism (γ' (S'.affineBasicOpen f))
      (S'.presheaf.map (homOfLE (S'.basicOpen_le f)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (s' : S' ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable {X Y : Scheme.{u}} (x₀ : X ⟶ I.subscheme) (y₀ : Y ⟶ I'.subscheme)
variable (f : X ⟶ Y)
variable (g : DividedPowerSchemeHom I I' s s')
variable (h_comm : f ≫ y₀ = x₀ ≫ g.zeroFiberMap)
variable (h_dividedPowers_compatible :
  ∀ (V : S'.affineOpens) (W : S.affineOpens)
    (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
    (γ' V).IsDPMorphism (γ W) (g.base.appLE V W hVW).hom)
variable (pX : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (pY : ∀ U : Y.affineOpens, IsNilpotent (p : Γ(Y, U)))

/-- Under the sheafification, Kan extension, and left-exactness assumptions, a
compatible divided-power base map and source map induce a geometric morphism
from the target small crystalline topos to the source small crystalline topos.
It composes the target small-to-big inclusion, the conditional big crystalline
morphism, and the source big-to-small projection. -/
noncomputable def smallCrystallineToposHom
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) (Type (u + 1))]
    [HasWeakSheafify
      (crystallineZariskiTopology S' I' γ' h'_compatible Y y₀) (Type (u + 1))]
    [HasSheafify
      (smallCrystallineTopology p S' I' γ' h'_compatible s' Y y₀ pY)
      (Type (u + 1))]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P]
    [∀ P : (smallCrystallineSite S' I' γ' h'_compatible Y y₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S' I' γ' h'_compatible Y y₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (Functor.op (CrystallineFunctor.of f g h_comm pX pY
        h_dividedPowers_compatible).toRelativeFunctor).HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((CrystallineFunctor.of f g h_comm pX pY
        h_dividedPowers_compatible).toRelativeFunctor.sheafPullback (Type (u + 1))
        (crystallineZariskiTopology S I γ h_compatible X x₀)
        (crystallineZariskiTopology S' I' γ' h'_compatible Y y₀))] :
    MorphismOfTopoiIn
      (smallCrystallineTopology p S I γ h_compatible s X x₀ pX)
      (smallCrystallineTopology p S' I' γ' h'_compatible s' Y y₀ pY) :=
  MorphismOfTopoiIn.comp
    (bigToSmallCrystallineToposMorphism S I γ h_compatible X x₀ p s pX)
    (MorphismOfTopoiIn.comp
      (crystallineToposHom I I' γ γ' h_compatible h'_compatible s s' x₀ y₀ f g
        h_comm h_dividedPowers_compatible pX pY)
      (smallToBigCrystallineToposMorphism S' I' γ' h'_compatible Y y₀ p s' pY))

/-- The conditional geometric morphism from the target small crystalline topos
to the source small crystalline topos is the composite of the target inclusion,
the conditional big crystalline morphism, and the source projection. -/
theorem smallCrystallineToposHom_eq
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) (Type (u + 1))]
    [HasWeakSheafify
      (crystallineZariskiTopology S' I' γ' h'_compatible Y y₀) (Type (u + 1))]
    [HasSheafify
      (smallCrystallineTopology p S' I' γ' h'_compatible s' Y y₀ pY)
      (Type (u + 1))]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P]
    [∀ P : (smallCrystallineSite S' I' γ' h'_compatible Y y₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S' I' γ' h'_compatible Y y₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (Functor.op (CrystallineFunctor.of f g h_comm pX pY
        h_dividedPowers_compatible).toRelativeFunctor).HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((CrystallineFunctor.of f g h_comm pX pY
        h_dividedPowers_compatible).toRelativeFunctor.sheafPullback (Type (u + 1))
        (crystallineZariskiTopology S I γ h_compatible X x₀)
        (crystallineZariskiTopology S' I' γ' h'_compatible Y y₀))] :
    smallCrystallineToposHom I I' γ γ' h_compatible h'_compatible s s' x₀ y₀ f g
        h_comm h_dividedPowers_compatible pX pY =
      MorphismOfTopoiIn.comp
        (bigToSmallCrystallineToposMorphism S I γ h_compatible X x₀ p s pX)
        (MorphismOfTopoiIn.comp
          (crystallineToposHom I I' γ γ' h_compatible h'_compatible s s' x₀ y₀ f g
            h_comm h_dividedPowers_compatible pX pY)
          (smallToBigCrystallineToposMorphism S' I' γ' h'_compatible Y y₀ p s' pY)) :=
  sorry

/-- The inverse image of the conditional geometric morphism from the target
small crystalline topos to the source small crystalline topos is the composite
of the inverse images of the source projection, the conditional big crystalline
morphism, and the target inclusion. -/
theorem smallCrystallineToposHom_inverseImage
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) (Type (u + 1))]
    [HasWeakSheafify
      (crystallineZariskiTopology S' I' γ' h'_compatible Y y₀) (Type (u + 1))]
    [HasSheafify
      (smallCrystallineTopology p S' I' γ' h'_compatible s' Y y₀ pY)
      (Type (u + 1))]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P]
    [∀ P : (smallCrystallineSite S' I' γ' h'_compatible Y y₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S' I' γ' h'_compatible Y y₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (Functor.op (CrystallineFunctor.of f g h_comm pX pY
        h_dividedPowers_compatible).toRelativeFunctor).HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((CrystallineFunctor.of f g h_comm pX pY
        h_dividedPowers_compatible).toRelativeFunctor.sheafPullback (Type (u + 1))
        (crystallineZariskiTopology S I γ h_compatible X x₀)
        (crystallineZariskiTopology S' I' γ' h'_compatible Y y₀))] :
    (smallCrystallineToposHom I I' γ γ' h_compatible h'_compatible s s' x₀ y₀ f g
        h_comm h_dividedPowers_compatible pX pY).inverseImage =
      (bigToSmallCrystallineToposMorphism S I γ h_compatible X x₀ p s pX).inverseImage ⋙
        (crystallineToposHom I I' γ γ' h_compatible h'_compatible s s' x₀ y₀ f g
          h_comm h_dividedPowers_compatible pX pY).inverseImage ⋙
        (smallToBigCrystallineToposMorphism S' I' γ' h'_compatible Y y₀ p s' pY).inverseImage :=
  sorry

end Functoriality

end AlgebraicGeometry
