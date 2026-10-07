module

public import stacks_project.Chap60.Remark_60_8_5_Functoriality
public import stacks_project.Chap60.Remark_60_8_7_Structure_morphism
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.Big
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

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

/-- Remark 60.8.8 (Compatibilities): in the functoriality situation of
Remark 60.8.5, the underlying morphisms of topoi form a commutative square.
The equality of inverse-image functors expresses the two routes from sheaves on
the big Zariski topos of `S'` to sheaves on the crystalline topos of `Y/S'`.
-/
@[stacks 07MG]
theorem crystallineToposHom_bigStructureMorphism
    (pX : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (pY : ∀ U : Y.affineOpens, IsNilpotent (p : Γ(Y, U)))
    [HasWeakSheafify
      (crystallineZariskiTopology S' I' γ' h'_compatible Y y₀)
      (Type (u + 1))]
    [∀ P : (RelativeCRIS S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (Functor.op (CrystallineFunctor.of f g h_comm pX pY
        h_dividedPowers_compatible).toRelativeFunctor).HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((CrystallineFunctor.of f g h_comm pX pY
        h_dividedPowers_compatible).toRelativeFunctor.sheafPullback (Type (u + 1))
        (crystallineZariskiTopology S I γ h_compatible X x₀)
        (crystallineZariskiTopology S' I' γ' h'_compatible Y y₀))]
    [HasSheafify
      (crystallineZariskiTopology S I γ h_compatible X x₀)
      (Type (u + 1))]
    [∀ P : (RelativeCRIS S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (bigStructureFunctor S I γ h_compatible s X x₀ pX).op.HasPointwiseRightKanExtension P]
    [HasSheafify
      (crystallineZariskiTopology S' I' γ' h'_compatible Y y₀)
      (Type (u + 1))]
    [∀ P : (RelativeCRIS S' I' γ' h'_compatible Y y₀)ᵒᵖ ⥤ Type (u + 1),
      (bigStructureFunctor S' I' γ' h'_compatible s' Y y₀ pY).op.HasPointwiseRightKanExtension P] :
    (Zariski.Big.morphismOfTopoi g.base).inverseImage ⋙
        (bigStructureMorphism S I γ h_compatible s X x₀ pX).inverseImage ⋙
        (crystallineToposHom I I' γ γ' h_compatible h'_compatible s s' x₀ y₀ f g
          h_comm h_dividedPowers_compatible pX pY).inverseImage =
      (bigStructureMorphism S' I' γ' h'_compatible s' Y y₀ pY).inverseImage := sorry

end Compatibilities

end AlgebraicGeometry.Scheme.Crystalline

end
