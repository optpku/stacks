module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Limits.OverPost
public import stacks_project.Chap60.Lemma_60_9_5_Functor
public import stacks_project.Chap60.Lemma_60_9_5_Topos

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline

universe u

noncomputable section

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {S S' X X' : Scheme.{u}}
variable (iS : S' ⟶ S) [IsOpenImmersion iS]
variable (iX : X' ⟶ X) [IsOpenImmersion iX]

variable (I : S.IdealSheafData) (I' : S'.IdealSheafData)
variable (h_I'_restrict : I' = I.comap iS)
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
variable (h_s'_restrict : s' = iS ≫ s)
variable (x₀ : X ⟶ I.subscheme) (x₀' : X' ⟶ I'.subscheme)
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (h_p' : ∀ U : X'.affineOpens, IsNilpotent (p : Γ(X', U)))

variable (g : DividedPowerSchemeHom I' I s' s)
variable (h_g : g.base = iS)
variable (h_comm : iX ≫ x₀ = x₀' ≫ g.zeroFiberMap)
variable (h_dividedPowers :
  ∀ (V : S.affineOpens) (W : S'.affineOpens)
    (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
    (γ V).IsDPMorphism (γ' W) (g.base.appLE V W hVW).hom)

include h_I'_restrict h_s'_restrict h_g

/--
Lemma 60.9.5 (1): the crystalline functor attached to the open inclusions is fully faithful.
The source-side setup is `I'` on `S'` and `x₀' : X' ⟶ I'.subscheme`; the target-side setup is
`I` on `S` and `x₀ : X ⟶ I.subscheme`.
-/
@[stacks 07KL]
noncomputable def crystallineOpenSubschemeFullyFaithful :
    (openCrystallineSmallFunctor iX I I' γ γ' h_compatible h'_compatible s s'
      x₀ x₀' h_p h_p' g h_comm h_dividedPowers).FullyFaithful where
  preimage := openCrystallineHomPreimage iX I I' γ γ' h_compatible h'_compatible
    s s' x₀ x₀' h_p h_p' g h_comm h_dividedPowers
  map_preimage := openCrystallineSmallFunctor_map_preimage iX I I' γ γ'
    h_compatible h'_compatible s s' x₀ x₀' h_p h_p' g h_comm h_dividedPowers
  preimage_map := openCrystallineSmallFunctor_preimage_map iX I I' γ γ'
    h_compatible h'_compatible s s' x₀ x₀' h_p h_p' g h_comm h_dividedPowers

/--
Lemma 60.9.5 (2): the morphism of crystalline topoi induced by the open-restriction functor
fits with the canonical small-Zariski morphism into the displayed commutative square.
-/
@[stacks 07KL]
noncomputable def crystallineOpenSubschemeToposSquare
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
        (smallCrystallineToposMorphism S' I' γ' h'_compatible s' X' x₀' h_p').inverseImage ≅
      (smallCrystallineToposMorphism S I γ h_compatible s X x₀ h_p).inverseImage ⋙
        (openCrystallineToposMorphism iX I I' γ γ' h_compatible h'_compatible s s'
          x₀ x₀' h_p h_p' g h_comm h_dividedPowers).inverseImage :=
  eqToIso (openCrystallineToposSquare_comm iX I I' γ γ' h_compatible h'_compatible
    s s' x₀ x₀' h_p h_p' g h_comm h_dividedPowers)

omit h_I'_restrict h_s'_restrict h_g

/--
Lemma 60.9.5 (3): the displayed square is the Sites 7.31.1 localization of
`u_{X/S}` at the sheafified representable `h_{X'}`. Equivalently, the inverse-image
composites of that localization square are
`Over.star h_{X'} ⋙ (u_{X/S}.localization h_{X'}).inverseImage` and
`u_{X/S}^{-1} ⋙ Over.star (u_{X/S}^{-1} h_{X'})`.
-/
@[stacks 07KL]
noncomputable def crystallineOpenSubschemeLocalization
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (Functor.op (forgetfulFunctor p S I γ h_compatible s X x₀ h_p)).HasPointwiseRightKanExtension P]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (Type (u + 1))]
    [HasWeakSheafify X.smallZariskiTopology (Type (u + 1))]
    [HasPullbacks (Sheaf X.smallZariskiTopology (Type (u + 1)))]
    [HasBinaryProducts (Sheaf X.smallZariskiTopology (Type (u + 1)))]
    [HasBinaryProducts
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) (Type (u + 1)))] :
    Over.star (openSubschemeRepresentable iX) ⋙
        ((smallCrystallineToposMorphism S I γ h_compatible s X x₀ h_p).localization
          (openSubschemeRepresentable iX)).inverseImage ≅
      (smallCrystallineToposMorphism S I γ h_compatible s X x₀ h_p).inverseImage ⋙
        Over.star
          ((smallCrystallineToposMorphism S I γ h_compatible s X x₀ h_p).inverseImage.obj
            (openSubschemeRepresentable iX)) :=
  TwoSquare.overPost.rightAdjointIso
    (smallCrystallineToposMorphism S I γ h_compatible s X x₀ h_p).inverseImage
    (openSubschemeRepresentable iX)

/-- The 7.31.1 localization square for `u_{X/S}` at `h_{X'}` is an isomorphism of inverse images. -/
theorem crystallineOpenSubschemeLocalization_isIso
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (Functor.op (forgetfulFunctor p S I γ h_compatible s X x₀ h_p)).HasPointwiseRightKanExtension P]
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (Type (u + 1))]
    [HasWeakSheafify X.smallZariskiTopology (Type (u + 1))]
    [HasPullbacks (Sheaf X.smallZariskiTopology (Type (u + 1)))]
    [HasBinaryProducts (Sheaf X.smallZariskiTopology (Type (u + 1)))]
    [HasBinaryProducts
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) (Type (u + 1)))] :
    IsIso (crystallineOpenSubschemeLocalization iX I γ h_compatible s x₀ h_p).hom := sorry
end
