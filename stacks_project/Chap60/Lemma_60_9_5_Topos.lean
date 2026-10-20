/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.Topos.Subtopos.Slice
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.SmallToBig
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import stacks_project.Chap60.Lemma_60_9_5_Functor
public import stacks_project.Chap60.Remark_60_9_4_Comparison_with_Zariski_site_Comparison

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline

universe u

noncomputable section

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {S S' X X' : Scheme.{u}}
variable (iX : X' ⟶ X) [IsOpenImmersion iX]

variable (I : S.IdealSheafData) (I' : S'.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (γ' : ∀ V : S'.affineOpens, DividedPowers (I'.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (g : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen g))
      (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom)
variable (h'_compatible :
  ∀ (V : S'.affineOpens) (g : Γ(S', V)),
    (γ' V).IsDPMorphism (γ' (S'.affineBasicOpen g))
      (S'.presheaf.map (homOfLE (S'.basicOpen_le g)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (s' : S' ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (x₀ : X ⟶ I.subscheme) (x₀' : X' ⟶ I'.subscheme)
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (h_p' : ∀ U : X'.affineOpens, IsNilpotent (p : Γ(X', U)))

variable (g : DividedPowerSchemeHom I' I s' s)
variable (h_comm : iX ≫ x₀ = x₀' ≫ g.zeroFiberMap)
variable (h_dividedPowers :
  ∀ (V : S.affineOpens) (W : S'.affineOpens)
    (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
    (γ V).IsDPMorphism (γ' W) (g.base.appLE V W hVW).hom)

/-- The morphism of small crystalline topoi induced by open restriction. -/
def openCrystallineToposMorphism
    [(openCrystallineSmallFunctor iX I I' γ γ' h_compatible h'_compatible s s'
      x₀ x₀' h_p h_p' g h_comm h_dividedPowers).IsCocontinuous
        (smallCrystallineTopology p S' I' γ' h'_compatible s' X' x₀' h_p')
        (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)]
    [∀ P : (smallCrystallineSite S' I' γ' h'_compatible X' x₀')ᵒᵖ ⥤ Type (u + 1),
      (Functor.op (openCrystallineSmallFunctor iX I I' γ γ' h_compatible h'_compatible
        s s' x₀ x₀' h_p h_p' g h_comm h_dividedPowers)).HasPointwiseRightKanExtension P]
    [HasSheafify
      (smallCrystallineTopology p S' I' γ' h'_compatible s' X' x₀' h_p')
      (Type (u + 1))] :
    MorphismOfTopoiIn
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (smallCrystallineTopology p S' I' γ' h'_compatible s' X' x₀' h_p') :=
  (openCrystallineSmallFunctor iX I I' γ γ' h_compatible h'_compatible s s'
    x₀ x₀' h_p h_p' g h_comm h_dividedPowers).morphismOfTopoiInOfCocontinuous
      (smallCrystallineTopology p S' I' γ' h'_compatible s' X' x₀' h_p')
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)

/-- The sheafified representable on `X.smallZariskiTopology` associated to `X' ⟶ X`. -/
noncomputable def openSubschemeRepresentable
    [HasWeakSheafify X.smallZariskiTopology (Type (u + 1))] :
    Sheaf X.smallZariskiTopology (Type (u + 1)) :=
  X.smallZariskiTopology.uliftSheafifiedRepresentable.{u + 1}
    (MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) iX
      (inferInstance : IsOpenImmersion iX))

/-- Commutativity of inverse images in the open crystalline/Zariski square. -/
theorem openCrystallineToposSquare_comm
    [(openCrystallineSmallFunctor iX I I' γ γ' h_compatible h'_compatible s s'
      x₀ x₀' h_p h_p' g h_comm h_dividedPowers).IsCocontinuous
        (smallCrystallineTopology p S' I' γ' h'_compatible s' X' x₀' h_p')
        (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)]
    [∀ P : (smallCrystallineSite S' I' γ' h'_compatible X' x₀')ᵒᵖ ⥤ Type (u + 1),
      (Functor.op (openCrystallineSmallFunctor iX I I' γ γ' h_compatible h'_compatible
        s s' x₀ x₀' h_p h_p' g h_comm h_dividedPowers)).HasPointwiseRightKanExtension P]
    [∀ P : (smallCrystallineSite S' I' γ' h'_compatible X' x₀')ᵒᵖ ⥤ Type (u + 1),
      (Functor.op (forgetfulFunctor p S' I' γ' h'_compatible s' X' x₀' h_p')).HasPointwiseRightKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (Functor.op (forgetfulFunctor p S I γ h_compatible s X x₀ h_p)).HasPointwiseRightKanExtension P]
    [HasSheafify
      (smallCrystallineTopology p S' I' γ' h'_compatible s' X' x₀' h_p')
      (Type (u + 1))]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (Type (u + 1))] :
    (Zariski.SmallToBig.smallMorphism iX).inverseImage ⋙
        (smallCrystallineToposMorphism S' I' γ' h'_compatible s' X' x₀' h_p').inverseImage =
      (smallCrystallineToposMorphism S I γ h_compatible s X x₀ h_p).inverseImage ⋙
        (openCrystallineToposMorphism iX I I' γ γ' h_compatible h'_compatible s s'
          x₀ x₀' h_p h_p' g h_comm h_dividedPowers).inverseImage := sorry

/-- The small Zariski inverse image along an open immersion is an equivalence. -/
instance crystallineOpenSubschemeZariskiLocalization
    [HasWeakSheafify X.smallZariskiTopology (Type (u + 1))] :
    (Zariski.SmallToBig.smallMorphism iX).inverseImage.IsEquivalence := sorry

/-- The localized inverse image is computed objectwise by `u_{X/S}`. -/
theorem crystallineOpenSubschemeLocalization_inverseImage_obj
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (Functor.op (forgetfulFunctor p S I γ h_compatible s X x₀ h_p)).HasPointwiseRightKanExtension P]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (Type (u + 1))]
    [HasWeakSheafify X.smallZariskiTopology (Type (u + 1))]
    [HasPullbacks (Sheaf X.smallZariskiTopology (Type (u + 1)))]
    (Z : Over (openSubschemeRepresentable iX)) :
    ((smallCrystallineToposMorphism S I γ h_compatible s X x₀ h_p).localization
      (openSubschemeRepresentable iX)).inverseImage.obj Z =
      Over.mk ((smallCrystallineToposMorphism S I γ h_compatible s X x₀ h_p).inverseImage.map
        Z.hom) := sorry

end
