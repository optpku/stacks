/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.SmallToBig
public import stacks_project.Chap60.Remark_60_9_4_Comparison_with_Zariski_site_Comparison

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

/-- Remark 60.9.6 (Structure morphism).
In Situation 60.7.5, with `S0 = I.subscheme` and structure morphism `x₀ : X ⟶ S0`,
the crystalline structure morphism `τ_{X/S}` is the morphism of topoi
`(X/S)_cris ⟶ Sh(S_Zar)` obtained by the lower route
`u_{X/S}` then `f_small = Zariski.SmallToBig.smallMorphism x₀` then
`Zariski.SmallToBig.smallMorphism I.subschemeι`. This composite is defined even
when `p` is not locally nilpotent on `S0`. -/
@[stacks 07IM]
noncomputable def crystallineStructureMorphism {p : ℕ} [Fact (Nat.Prime p)]
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
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (Type (u + 1))]
    [HasSheafify X.smallZariskiTopology (Type (u + 1))]
    [HasSheafify I.subscheme.smallZariskiTopology (Type (u + 1))]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P] :
    MorphismOfTopoiIn S.smallZariskiTopology
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) :=
  MorphismOfTopoiIn.comp
    (MorphismOfTopoiIn.comp
      (Zariski.SmallToBig.smallMorphism I.subschemeι)
      (Zariski.SmallToBig.smallMorphism x₀))
    (smallCrystallineToposMorphism S I γ h_compatible s X x₀ h_p)

/-- The inverse image of `crystallineStructureMorphism` is the composite of the
three inverse images along `u_{X/S}`, `f_small`, and `S0 → S`. -/
theorem crystallineStructureMorphism_inverseImage {p : ℕ} [Fact (Nat.Prime p)]
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
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (Type (u + 1))]
    [HasSheafify X.smallZariskiTopology (Type (u + 1))]
    [HasSheafify I.subscheme.smallZariskiTopology (Type (u + 1))]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P] :
    (crystallineStructureMorphism S I γ h_compatible s X x₀ h_p).inverseImage =
      (Zariski.SmallToBig.smallMorphism I.subschemeι).inverseImage ⋙
        (Zariski.SmallToBig.smallMorphism x₀).inverseImage ⋙
          (smallCrystallineToposMorphism S I γ h_compatible s X x₀ h_p).inverseImage :=
    sorry

end AlgebraicGeometry.Scheme.Crystalline
