/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.Remark_60_8_5_Functoriality
public import stacks_project.Chap60.Lemma_60_9_2_Topos

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
open scoped MorphismOfTopoiIn

universe u

namespace CrystallineBaseChangeGeometry

variable {p : ℕ} [Fact p.Prime]
variable {S S' X Y : Scheme.{u}} (I : S.IdealSheafData) (I' : S'.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (γ' : ∀ V : S'.affineOpens, DividedPowers (I'.ideal V))
variable (hc : ∀ (V : S.affineOpens) (f : Γ(S, V)),
  (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
    (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (hc' : ∀ (V : S'.affineOpens) (f : Γ(S', V)),
  (γ' V).IsDPMorphism (γ' (S'.affineBasicOpen f))
    (S'.presheaf.map (homOfLE (S'.basicOpen_le f)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (s' : S' ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (x₀ : X ⟶ I.subscheme) (y₀ : Y ⟶ I'.subscheme)
variable (f : X ⟶ Y) (g : DividedPowerSchemeHom I I' s s')
variable (hf : f ≫ y₀ = x₀ ≫ g.zeroFiberMap)
variable (hγ : ∀ (V : S'.affineOpens) (W : S.affineOpens)
  (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
  (γ' V).IsDPMorphism (γ W) (g.base.appLE V W hVW).hom)
variable (hpX : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (hpY : ∀ U : Y.affineOpens, IsNilpotent (p : Γ(Y, U)))
variable [HasSheafify (crystallineZariskiTopology S I γ hc X x₀) (Type (u + 1))]
variable [∀ P : (RelativeCRIS S I γ hc X x₀)ᵒᵖ ⥤ Type (u + 1),
  ((CrystallineFunctor.of f g hf hpX hpY hγ).toRelativeFunctor).op.HasPointwiseRightKanExtension P]

/-- The geometric big crystalline morphism has direction `(X/S) → (Y/S')`.
Since `MorphismOfTopoiIn J K` means `Sh(K) → Sh(J)`, its topology arguments
are reversed. The cocontinuous construction supplies the actual adjunction. -/
noncomputable def bigMorphism :
    MorphismOfTopoiIn (crystallineZariskiTopology S' I' γ' hc' Y y₀)
      (crystallineZariskiTopology S I γ hc X x₀) :=
  (CrystallineFunctor.of f g hf hpX hpY hγ).toRelativeFunctor.morphismOfTopoiInOfCocontinuous
    (crystallineZariskiTopology S I γ hc X x₀)
    (crystallineZariskiTopology S' I' γ' hc' Y y₀)

variable [HasWeakSheafify (crystallineZariskiTopology S' I' γ' hc' Y y₀) (Type (u + 1))]
variable [HasSheafify (smallCrystallineTopology p S I γ hc s X x₀ hpX) (Type (u + 1))]
variable [∀ P : (smallCrystallineSite S I γ hc X x₀)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion S I γ hc X x₀).op.HasPointwiseRightKanExtension P]
variable [∀ P : (smallCrystallineSite S' I' γ' hc' Y y₀)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion S' I' γ' hc' Y y₀).op.HasLeftKanExtension P]

/-- The small crystalline morphism is `π_Y ∘ f_CRIS ∘ i_X`, retaining the
same geometric direction as the input scheme map. -/
noncomputable def smallMorphism :
    MorphismOfTopoiIn (smallCrystallineTopology p S' I' γ' hc' s' Y y₀ hpY)
      (smallCrystallineTopology p S I γ hc s X x₀ hpX) :=
  MorphismOfTopoiIn.comp
    (bigToSmallCrystallineToposMorphism S' I' γ' hc' Y y₀ p s' hpY)
    (MorphismOfTopoiIn.comp (bigMorphism I I' γ γ' hc hc' s s' x₀ y₀ f g hf hγ hpX hpY)
      (smallToBigCrystallineToposMorphism S I γ hc X x₀ p s hpX))

end CrystallineBaseChangeGeometry
