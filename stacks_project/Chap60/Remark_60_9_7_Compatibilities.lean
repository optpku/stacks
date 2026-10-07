module

public import stacks_project.Chap60.Remark_60_9_3_Functoriality
public import stacks_project.Chap60.Remark_60_8_7_Structure_morphism
public import stacks_project.Chap60.Lemma_60_9_2_Topos
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.Big
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Crystalline
open Scheme.Zariski.Big
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable {p : ℕ} [Fact (Nat.Prime p)]
variable (S : Scheme.{u}) (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
variable (pX : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/-- The small crystalline structure morphism `(X/S)_cris ⟶ Sh((Sch/S)_Zar)`, as the
composite of `smallToBigCrystallineToposMorphism` with `bigStructureMorphism`. -/
noncomputable def smallStructureMorphism
    [HasSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀)
      (Type (u + 1))]
    [∀ P : (RelativeCRIS S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (bigStructureFunctor S I γ h_compatible s X x₀ pX).op.HasPointwiseRightKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasPointwiseRightKanExtension P]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ pX)
      (Type (u + 1))] :
    MorphismOfTopoiIn S.bigZariskiTopology
      (smallCrystallineTopology p S I γ h_compatible s X x₀ pX) :=
  MorphismOfTopoiIn.comp
    (bigStructureMorphism S I γ h_compatible s X x₀ pX)
    (smallToBigCrystallineToposMorphism S I γ h_compatible X x₀ p s pX)

/-- Unfolding of `smallStructureMorphism` as the composite of the big structure
morphism with the small-to-big crystalline topos morphism. -/
theorem smallStructureMorphism_eq
    [HasSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀)
      (Type (u + 1))]
    [∀ P : (RelativeCRIS S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (bigStructureFunctor S I γ h_compatible s X x₀ pX).op.HasPointwiseRightKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasPointwiseRightKanExtension P]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ pX)
      (Type (u + 1))] :
    smallStructureMorphism S I γ h_compatible s X x₀ pX =
      MorphismOfTopoiIn.comp
        (bigStructureMorphism S I γ h_compatible s X x₀ pX)
        (smallToBigCrystallineToposMorphism S I γ h_compatible X x₀ p s pX) :=
  sorry

end AlgebraicGeometry.Scheme.Crystalline

namespace AlgebraicGeometry

section Compatibilities

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

/-- Remark 60.9.7 (Compatibilities): in the situation of Remark 60.9.3, the small
crystalline topos morphism `f_cris : (X/S)_cris ⟶ (Y/S')_cris` and the big Zariski
morphism of topoi induced by `g.base : S ⟶ S'` form a commutative square whose
vertical arrows are the (unringed) structure morphisms
`(X/S)_cris ⟶ Sh((Sch/S)_Zar)` and `(Y/S')_cris ⟶ Sh((Sch/S')_Zar)`. The source
phrases this as a diagram of ringed topoi; the current crystalline maps are the
underlying morphisms of topoi. -/
@[stacks 07MH]
theorem smallCrystallineStructureMorphism_commSq
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) (Type (u + 1))]
    [HasWeakSheafify
      (crystallineZariskiTopology S' I' γ' h'_compatible Y y₀) (Type (u + 1))]
    [HasSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) (Type (u + 1))]
    [HasSheafify
      (crystallineZariskiTopology S' I' γ' h'_compatible Y y₀) (Type (u + 1))]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ pX) (Type (u + 1))]
    [HasSheafify
      (smallCrystallineTopology p S' I' γ' h'_compatible s' Y y₀ pY) (Type (u + 1))]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (smallCrystallineSite S' I' γ' h'_compatible Y y₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S' I' γ' h'_compatible Y y₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (Functor.op (CrystallineFunctor.of f g h_comm pX pY
        h_dividedPowers_compatible).toRelativeFunctor).HasLeftKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (bigStructureFunctor S I γ h_compatible s X x₀ pX).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S' I' γ' h'_compatible Y y₀)ᵒᵖ ⥤ Type (u + 1),
      (bigStructureFunctor S' I' γ' h'_compatible s' Y y₀ pY).op.HasPointwiseRightKanExtension P]
    [PreservesFiniteLimits
      ((CrystallineFunctor.of f g h_comm pX pY
        h_dividedPowers_compatible).toRelativeFunctor.sheafPullback (Type (u + 1))
        (crystallineZariskiTopology S I γ h_compatible X x₀)
        (crystallineZariskiTopology S' I' γ' h'_compatible Y y₀))] :
    MorphismOfTopoiIn.comp
        (morphismOfTopoi g.base)
        (MorphismOfTopoiIn.comp
          (smallStructureMorphism S I γ h_compatible s X x₀ pX)
          (smallCrystallineToposHom I I' γ γ' h_compatible h'_compatible s s' x₀ y₀ f g
            h_comm h_dividedPowers_compatible pX pY)) =
      smallStructureMorphism S' I' γ' h'_compatible s' Y y₀ pY :=
  sorry

/-- Inverse-image functors of the two composites in
`smallCrystallineStructureMorphism_commSq` agree. -/
theorem smallCrystallineStructureMorphism_inverseImage_commSq
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) (Type (u + 1))]
    [HasWeakSheafify
      (crystallineZariskiTopology S' I' γ' h'_compatible Y y₀) (Type (u + 1))]
    [HasSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀) (Type (u + 1))]
    [HasSheafify
      (crystallineZariskiTopology S' I' γ' h'_compatible Y y₀) (Type (u + 1))]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ pX) (Type (u + 1))]
    [HasSheafify
      (smallCrystallineTopology p S' I' γ' h'_compatible s' Y y₀ pY) (Type (u + 1))]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasLeftKanExtension P]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S I γ h_compatible X x₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (smallCrystallineSite S' I' γ' h'_compatible Y y₀)ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineInclusion S' I' γ' h'_compatible Y y₀).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (Functor.op (CrystallineFunctor.of f g h_comm pX pY
        h_dividedPowers_compatible).toRelativeFunctor).HasLeftKanExtension P]
    [∀ P : (RelativeCRIS S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (bigStructureFunctor S I γ h_compatible s X x₀ pX).op.HasPointwiseRightKanExtension P]
    [∀ P : (RelativeCRIS S' I' γ' h'_compatible Y y₀)ᵒᵖ ⥤ Type (u + 1),
      (bigStructureFunctor S' I' γ' h'_compatible s' Y y₀ pY).op.HasPointwiseRightKanExtension P]
    [PreservesFiniteLimits
      ((CrystallineFunctor.of f g h_comm pX pY
        h_dividedPowers_compatible).toRelativeFunctor.sheafPullback (Type (u + 1))
        (crystallineZariskiTopology S I γ h_compatible X x₀)
        (crystallineZariskiTopology S' I' γ' h'_compatible Y y₀))] :
    (MorphismOfTopoiIn.comp
        (morphismOfTopoi g.base)
        (MorphismOfTopoiIn.comp
          (smallStructureMorphism S I γ h_compatible s X x₀ pX)
          (smallCrystallineToposHom I I' γ γ' h_compatible h'_compatible s s' x₀ y₀ f g
            h_comm h_dividedPowers_compatible pX pY))).inverseImage =
      (smallStructureMorphism S' I' γ' h'_compatible s' Y y₀ pY).inverseImage :=
  sorry

end Compatibilities

end AlgebraicGeometry

end
