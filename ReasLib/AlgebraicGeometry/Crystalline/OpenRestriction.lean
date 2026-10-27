/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Functoriality
public import ReasLib.AlgebraicGeometry.Crystalline.ZariskiComparison
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.SmallToBig
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Crystalline

section Raw

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {S S' X X' : Scheme.{u}}
variable (iX : X' ⟶ X) [hiX : IsOpenImmersion iX]

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

variable (base : S' ⟶ S)
variable (zeroFiberMap : I'.subscheme ⟶ I.subscheme)
variable (zeroFiber_comm : zeroFiberMap ≫ I.subschemeι = I'.subschemeι ≫ base)
variable (base_over : base ≫ s = s')
variable (ideal_compatible : I.comap base ≤ I')
variable (h_comm : iX ≫ x₀ = x₀' ≫ zeroFiberMap)
variable (h_dividedPowers :
  ∀ (V : S.affineOpens) (W : S'.affineOpens)
    (hVW : W.1 ≤ base ⁻¹ᵁ V.1),
    (γ V).IsDPMorphism (γ' W) (base.appLE V W hVW).hom)

include hiX in
/-- Composing an open crystalline source with an open immersion preserves smallness. -/
theorem openRestriction_mapsToSmall :
    smallCrystallineProperty S' I' γ' h'_compatible X' x₀' ≤
      (smallCrystallineProperty S I γ h_compatible X x₀).inverseImage
        (mapFunctor iX base zeroFiberMap zeroFiber_comm h_comm h_dividedPowers
          s' s base_over ideal_compatible h_p' h_p) := sorry

/-- Restriction along a compatible open source map retains the crystalline thickening. -/
def openRestrictionFunctor :
    smallCrystallineSite S' I' γ' h'_compatible X' x₀' ⥤
      smallCrystallineSite S I γ h_compatible X x₀ :=
  ObjectProperty.FullSubcategory.restrict (mapFunctor iX base zeroFiberMap zeroFiber_comm h_comm h_dividedPowers
          s' s base_over ideal_compatible h_p' h_p)
    (openRestriction_mapsToSmall iX I I' γ γ' h_compatible h'_compatible s s'
      x₀ x₀' h_p h_p' base zeroFiberMap zeroFiber_comm base_over
      ideal_compatible h_comm h_dividedPowers)

variable [hbase : IsOpenImmersion base]

/-- A morphism between restricted crystalline objects lifts by retaining its two component maps. -/
def openRestrictionHomPreimage
    {A B : smallCrystallineSite S' I' γ' h'_compatible X' x₀'}
    (φ : (openRestrictionFunctor iX I I' γ γ' h_compatible h'_compatible s s'
      x₀ x₀' h_p h_p' base zeroFiberMap zeroFiber_comm base_over
      ideal_compatible h_comm h_dividedPowers).obj A ⟶ (openRestrictionFunctor iX I I' γ γ' h_compatible h'_compatible s s'
      x₀ x₀' h_p h_p' base zeroFiberMap zeroFiber_comm base_over
      ideal_compatible h_comm h_dividedPowers).obj B) : A ⟶ B :=
  ObjectProperty.homMk
    { source := Over.homMk φ.hom.source.left (by
        apply (cancel_mono iX).1
        have h := φ.hom.source.w
        change φ.hom.source.left ≫ (B.obj.1.source.hom ≫ iX) =
          A.obj.1.source.hom ≫ iX at h
        exact (Category.assoc _ _ _).trans h)
      thickening := φ.hom.thickening
      source_comm := φ.hom.source_comm
      base_comm := by
        apply (cancel_mono base).1
        have h := φ.hom.base_comm
        change φ.hom.thickening ≫ (B.obj.1.thickeningToBase ≫ base) =
          A.obj.1.thickeningToBase ≫ base at h
        exact (Category.assoc _ _ _).trans h
      ideal_compatible := φ.hom.ideal_compatible
      dividedPowers_compatible := φ.hom.dividedPowers_compatible }

/-- Applying open restriction to the lifted morphism recovers the given morphism. -/
theorem openRestrictionFunctor_map_preimage
    {A B : smallCrystallineSite S' I' γ' h'_compatible X' x₀'}
    (φ : (openRestrictionFunctor iX I I' γ γ' h_compatible h'_compatible s s'
      x₀ x₀' h_p h_p' base zeroFiberMap zeroFiber_comm base_over
      ideal_compatible h_comm h_dividedPowers).obj A ⟶ (openRestrictionFunctor iX I I' γ γ' h_compatible h'_compatible s s'
      x₀ x₀' h_p h_p' base zeroFiberMap zeroFiber_comm base_over
      ideal_compatible h_comm h_dividedPowers).obj B) :
    (openRestrictionFunctor iX I I' γ γ' h_compatible h'_compatible s s'
      x₀ x₀' h_p h_p' base zeroFiberMap zeroFiber_comm base_over
      ideal_compatible h_comm h_dividedPowers).map (openRestrictionHomPreimage iX I I' γ γ' h_compatible h'_compatible s s'
      x₀ x₀' h_p h_p' base zeroFiberMap zeroFiber_comm base_over
      ideal_compatible h_comm h_dividedPowers φ) = φ := sorry

/-- Lifting an open restriction of a morphism recovers the original morphism. -/
theorem openRestrictionFunctor_preimage_map
    {A B : smallCrystallineSite S' I' γ' h'_compatible X' x₀'} (φ : A ⟶ B) :
    openRestrictionHomPreimage iX I I' γ γ' h_compatible h'_compatible s s'
      x₀ x₀' h_p h_p' base zeroFiberMap zeroFiber_comm base_over
      ideal_compatible h_comm h_dividedPowers ((openRestrictionFunctor iX I I' γ γ' h_compatible h'_compatible s s'
      x₀ x₀' h_p h_p' base zeroFiberMap zeroFiber_comm base_over
      ideal_compatible h_comm h_dividedPowers).map φ) = φ := sorry

include hbase in
/-- Open restriction of small crystalline sites is cocontinuous. -/
instance openRestrictionFunctor_isCocontinuous :
    (openRestrictionFunctor iX I I' γ γ' h_compatible h'_compatible s s'
      x₀ x₀' h_p h_p' base zeroFiberMap zeroFiber_comm base_over
      ideal_compatible h_comm h_dividedPowers).IsCocontinuous
      (smallCrystallineTopology p S' I' γ' h'_compatible s' X' x₀' h_p')
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) := sorry

end Raw

section Bases

variable {p : ℕ} [Fact (Nat.Prime p)] (B B' : Base.{u} p)
variable (iX : B'.source ⟶ B.source) [IsOpenImmersion iX]
variable (g : DividedPowerSchemeHom B'.ideal B.ideal B'.toSpec B.toSpec)
variable [IsOpenImmersion g.base]
variable (h_comm : iX ≫ B.sourceToClosed = B'.sourceToClosed ≫ g.zeroFiberMap)
variable (h_dividedPowers :
  ∀ (V : B.scheme.affineOpens) (W : B'.scheme.affineOpens)
    (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
    (B.dividedPowers V).IsDPMorphism (B'.dividedPowers W)
      (g.base.appLE V W hVW).hom)

/-- Compatible open immersions induce a fully faithful functor on small crystalline sites. -/
def crystallineOpenSubschemeFullyFaithful : (openRestrictionFunctor iX B.ideal B'.ideal B.dividedPowers B'.dividedPowers
      B.compatible B'.compatible B.toSpec B'.toSpec B.sourceToClosed B'.sourceToClosed
      B.prime_nilpotent B'.prime_nilpotent g.base g.zeroFiberMap g.zeroFiber_comm
      g.base_over g.ideal_compatible h_comm h_dividedPowers).FullyFaithful where
  preimage := openRestrictionHomPreimage iX B.ideal B'.ideal B.dividedPowers B'.dividedPowers
      B.compatible B'.compatible B.toSpec B'.toSpec B.sourceToClosed B'.sourceToClosed
      B.prime_nilpotent B'.prime_nilpotent g.base g.zeroFiberMap g.zeroFiber_comm
      g.base_over g.ideal_compatible h_comm h_dividedPowers
  map_preimage := openRestrictionFunctor_map_preimage iX B.ideal B'.ideal B.dividedPowers B'.dividedPowers
      B.compatible B'.compatible B.toSpec B'.toSpec B.sourceToClosed B'.sourceToClosed
      B.prime_nilpotent B'.prime_nilpotent g.base g.zeroFiberMap g.zeroFiber_comm
      g.base_over g.ideal_compatible h_comm h_dividedPowers
  preimage_map := openRestrictionFunctor_preimage_map iX B.ideal B'.ideal B.dividedPowers B'.dividedPowers
      B.compatible B'.compatible B.toSpec B'.toSpec B.sourceToClosed B'.sourceToClosed
      B.prime_nilpotent B'.prime_nilpotent g.base g.zeroFiberMap g.zeroFiber_comm
      g.base_over g.ideal_compatible h_comm h_dividedPowers

variable [∀ P : (smallCrystallineSite B'.scheme B'.ideal B'.dividedPowers B'.compatible
    B'.source B'.sourceToClosed)ᵒᵖ ⥤ Type (u + 1),
  (openRestrictionFunctor iX B.ideal B'.ideal B.dividedPowers B'.dividedPowers
      B.compatible B'.compatible B.toSpec B'.toSpec B.sourceToClosed B'.sourceToClosed
      B.prime_nilpotent B'.prime_nilpotent g.base g.zeroFiberMap g.zeroFiber_comm
      g.base_over g.ideal_compatible h_comm h_dividedPowers).op.HasPointwiseRightKanExtension P]
variable [HasSheafify (smallCrystallineTopology p B'.scheme B'.ideal B'.dividedPowers B'.compatible
    B'.toSpec B'.source B'.sourceToClosed B'.prime_nilpotent) (Type (u + 1))]

/-- The cocontinuous open restriction functor induces the crystalline morphism of topoi. -/
def openCrystallineToposMorphism : MorphismOfTopoiIn (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible
    B.toSpec B.source B.sourceToClosed B.prime_nilpotent) (smallCrystallineTopology p B'.scheme B'.ideal B'.dividedPowers B'.compatible
    B'.toSpec B'.source B'.sourceToClosed B'.prime_nilpotent) :=
  (openRestrictionFunctor iX B.ideal B'.ideal B.dividedPowers B'.dividedPowers
      B.compatible B'.compatible B.toSpec B'.toSpec B.sourceToClosed B'.sourceToClosed
      B.prime_nilpotent B'.prime_nilpotent g.base g.zeroFiberMap g.zeroFiber_comm
      g.base_over g.ideal_compatible h_comm h_dividedPowers).morphismOfTopoiInOfCocontinuous (smallCrystallineTopology p B'.scheme B'.ideal B'.dividedPowers B'.compatible
    B'.toSpec B'.source B'.sourceToClosed B'.prime_nilpotent) (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible
    B.toSpec B.source B.sourceToClosed B.prime_nilpotent)

variable [∀ P : (smallCrystallineSite B'.scheme B'.ideal B'.dividedPowers B'.compatible
    B'.source B'.sourceToClosed)ᵒᵖ ⥤ Type (u + 1),
  (forgetfulFunctor p B'.scheme B'.ideal B'.dividedPowers B'.compatible
      B'.toSpec B'.source B'.sourceToClosed B'.prime_nilpotent).op.HasPointwiseRightKanExtension P]
variable [∀ P : (smallCrystallineSite B.scheme B.ideal B.dividedPowers B.compatible
    B.source B.sourceToClosed)ᵒᵖ ⥤ Type (u + 1),
  (forgetfulFunctor p B.scheme B.ideal B.dividedPowers B.compatible
      B.toSpec B.source B.sourceToClosed B.prime_nilpotent).op.HasPointwiseRightKanExtension P]
variable [HasSheafify (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible
    B.toSpec B.source B.sourceToClosed B.prime_nilpotent) (Type (u + 1))]
variable [HasSheafify B'.source.smallZariskiTopology (Type (u + 1))]

/-- The open crystalline and Zariski inverse-image composites are naturally isomorphic. -/
theorem crystallineOpenSubschemeToposSquare :
    Nonempty
      ((Zariski.SmallToBig.smallMorphism iX).inverseImage ⋙ (smallCrystallineToposMorphism B'.scheme B'.ideal B'.dividedPowers
    B'.compatible B'.toSpec B'.source B'.sourceToClosed B'.prime_nilpotent).inverseImage ≅
        (smallCrystallineToposMorphism B.scheme B.ideal B.dividedPowers
    B.compatible B.toSpec B.source B.sourceToClosed B.prime_nilpotent).inverseImage ⋙ (openCrystallineToposMorphism B B' iX g h_comm h_dividedPowers).inverseImage) := sorry

variable [HasWeakSheafify B.source.smallZariskiTopology (Type (u + 1))]
variable [HasPullbacks (Sheaf B.source.smallZariskiTopology (Type (u + 1)))]
variable [HasBinaryProducts (Sheaf B.source.smallZariskiTopology (Type (u + 1)))]
variable [HasBinaryProducts (Sheaf (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible
    B.toSpec B.source B.sourceToClosed B.prime_nilpotent) (Type (u + 1)))]

/-- Restricting the crystalline and Zariski topoi to compatible open subschemes identifies
both smaller topoi with the slices at the open representable and its crystalline inverse image,
compatibly with the open inverse images and the crystalline-to-Zariski inverse image. -/
theorem crystallineOpenSubschemeLocalization
    (h_I'_restrict : B'.ideal = B.ideal.comap g.base) :
    let h := B.source.smallZariskiTopology.uliftSheafifiedRepresentable.{u + 1}
      (MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) iX
        (inferInstance : IsOpenImmersion iX))
    let u := (smallCrystallineToposMorphism B.scheme B.ideal B.dividedPowers
    B.compatible B.toSpec B.source B.sourceToClosed B.prime_nilpotent)
    let u' := (smallCrystallineToposMorphism B'.scheme B'.ideal B'.dividedPowers
    B'.compatible B'.toSpec B'.source B'.sourceToClosed B'.prime_nilpotent)
    let jZ := (Zariski.SmallToBig.smallMorphism iX)
    let jC := (openCrystallineToposMorphism B B' iX g h_comm h_dividedPowers)
    ∃ (eZ : Sheaf B'.source.smallZariskiTopology (Type (u + 1)) ≌ Over h)
      (eC : Sheaf (smallCrystallineTopology p B'.scheme B'.ideal B'.dividedPowers B'.compatible
    B'.toSpec B'.source B'.sourceToClosed B'.prime_nilpotent) (Type (u + 1)) ≌ Over (u.inverseImage.obj h)),
      Nonempty (jZ.inverseImage ⋙ eZ.functor ≅ Over.star h) ∧
      Nonempty (jC.inverseImage ⋙ eC.functor ≅ Over.star (u.inverseImage.obj h)) ∧
      Nonempty (u'.inverseImage ⋙ eC.functor ≅ eZ.functor ⋙ Over.post u.inverseImage) := sorry

end Bases

end AlgebraicGeometry.Scheme.Crystalline
