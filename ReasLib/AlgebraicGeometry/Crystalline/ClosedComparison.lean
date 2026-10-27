/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Base
public import ReasLib.AlgebraicGeometry.Crystalline.Site
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.Continuous

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable (S : Scheme.{u}) (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)

/-- Postcomposing the source of a small crystalline object with `X ⟶ I.subscheme`
gives a relative crystalline object with the same divided-power thickening. -/
def closedSourceObject (T : smallCrystallineSite S I γ h_compatible X x₀) :
    RelativeCRIS S I γ h_compatible I.subscheme (𝟙 I.subscheme) :=
  ⟨{ source := Over.mk (T.obj.1.source.hom ≫ x₀)
     thickening := T.obj.1.thickening
     thickeningToBase := T.obj.1.thickeningToBase
     inclusion := T.obj.1.inclusion
     ideal := T.obj.1.ideal
     gamma := T.obj.1.gamma
     thickening_compatible := T.obj.1.thickening_compatible
     isThickening := T.obj.1.isThickening
     inclusion_isThickening := T.obj.1.inclusion_isThickening
     ideal_eq_ker := T.obj.1.ideal_eq_ker
     source_comm := sorry }, T.obj.2⟩

/-- A small crystalline morphism induces a morphism over the canonical closed
subscheme with its original source and thickening maps. -/
def closedSourceMap {T U : smallCrystallineSite S I γ h_compatible X x₀}
    (f : T ⟶ U) :
    closedSourceObject S I γ h_compatible X x₀ T ⟶
      closedSourceObject S I γ h_compatible X x₀ U where
  source := Over.homMk f.hom.source.left sorry
  thickening := f.hom.thickening
  source_comm := f.hom.source_comm
  base_comm := f.hom.base_comm
  ideal_compatible := f.hom.ideal_compatible
  dividedPowers_compatible := f.hom.dividedPowers_compatible

/-- Postcomposing crystalline sources preserves identity morphisms. -/
theorem closedSourceMap_id (T : smallCrystallineSite S I γ h_compatible X x₀) :
    closedSourceMap S I γ h_compatible X x₀ (𝟙 T) =
      𝟙 (closedSourceObject S I γ h_compatible X x₀ T) := sorry

/-- Postcomposing crystalline sources preserves composition of morphisms. -/
theorem closedSourceMap_comp {T U V : smallCrystallineSite S I γ h_compatible X x₀}
    (f : T ⟶ U) (g : U ⟶ V) :
    closedSourceMap S I γ h_compatible X x₀ (f ≫ g) =
      closedSourceMap S I γ h_compatible X x₀ f ≫
        closedSourceMap S I γ h_compatible X x₀ g := sorry

/-- The functor from small crystalline objects over `X` to big crystalline
objects over the canonical closed subscheme postcomposes their source maps. -/
def closedSourceFunctor : smallCrystallineSite S I γ h_compatible X x₀ ⥤
    RelativeCRIS S I γ h_compatible I.subscheme (𝟙 I.subscheme) where
  obj := closedSourceObject S I γ h_compatible X x₀
  map := closedSourceMap S I γ h_compatible X x₀
  map_id := closedSourceMap_id S I γ h_compatible X x₀
  map_comp := closedSourceMap_comp S I γ h_compatible X x₀

variable (p : ℕ) [Fact p.Prime]
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/-- Postcomposition of crystalline sources to the canonical closed subscheme
is cocontinuous for the crystalline Zariski topologies. -/
instance closedSourceFunctor_isCocontinuous :
    (closedSourceFunctor S I γ h_compatible X x₀).IsCocontinuous
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (crystallineZariskiTopology S I γ h_compatible I.subscheme (𝟙 I.subscheme)) := sorry

variable (h_p₀ : ∀ U : I.subscheme.affineOpens, IsNilpotent (p : Γ(I.subscheme, U)))

/-- The small-to-big crystalline inclusion over the canonical closed subscheme
is continuous for the crystalline Zariski topologies. -/
instance closedInclusion_isContinuous :
    (smallCrystallineProperty S I γ h_compatible I.subscheme (𝟙 I.subscheme)).ι.IsContinuous
      (smallCrystallineTopology p S I γ h_compatible s I.subscheme (𝟙 I.subscheme) h_p₀)
      (crystallineZariskiTopology S I γ h_compatible I.subscheme (𝟙 I.subscheme)) := sorry

/-- Sheaf pullback along the small-to-big crystalline inclusion over the
canonical closed subscheme preserves finite limits. -/
instance closedInclusion_pullback_preservesFiniteLimits
    [HasWeakSheafify
      (crystallineZariskiTopology S I γ h_compatible I.subscheme (𝟙 I.subscheme))
      (Type (u + 1))]
    [∀ P : (smallCrystallineSite S I γ h_compatible I.subscheme (𝟙 I.subscheme))ᵒᵖ ⥤
        Type (u + 1),
      (smallCrystallineProperty S I γ h_compatible I.subscheme (𝟙 I.subscheme)).ι.op.HasLeftKanExtension P] :
    PreservesFiniteLimits
      ((smallCrystallineProperty S I γ h_compatible I.subscheme (𝟙 I.subscheme)).ι.sheafPullback
        (Type (u + 1))
        (smallCrystallineTopology p S I γ h_compatible s I.subscheme (𝟙 I.subscheme) h_p₀)
        (crystallineZariskiTopology S I γ h_compatible I.subscheme (𝟙 I.subscheme))) := sorry

namespace Base

variable {p : ℕ} [Fact p.Prime] (B : Base.{u} p)

/-- Replacing the source by the canonical closed subscheme gives a crystalline
base when the prime is locally nilpotent there. -/
def closedBase
    (h_p₀ : ∀ U : B.ideal.subscheme.affineOpens, IsNilpotent (p : Γ(B.ideal.subscheme, U))) :
    Base p :=
  { B with source := B.ideal.subscheme
           sourceToClosed := 𝟙 B.ideal.subscheme
           prime_nilpotent := h_p₀ }

/-- The crystalline morphism to the canonical closed subscheme is induced by
postcomposition of sources followed by the big-to-small crystalline morphism. -/
def closedCrystallineMorphism
    (h_p₀ : ∀ U : B.ideal.subscheme.affineOpens, IsNilpotent (p : Γ(B.ideal.subscheme, U)))
    [HasSheafify
      (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
        B.source B.sourceToClosed B.prime_nilpotent) (Type (u + 1))]
    [HasWeakSheafify
      (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
        B.ideal.subscheme (𝟙 B.ideal.subscheme)) (Type (u + 1))]
    [∀ P : (smallCrystallineSite B.scheme B.ideal B.dividedPowers B.compatible
        B.source B.sourceToClosed)ᵒᵖ ⥤ Type (u + 1),
      (closedSourceFunctor B.scheme B.ideal B.dividedPowers B.compatible
        B.source B.sourceToClosed).op.HasPointwiseRightKanExtension P]
    [∀ P : (smallCrystallineSite B.scheme B.ideal B.dividedPowers B.compatible
        B.ideal.subscheme (𝟙 B.ideal.subscheme))ᵒᵖ ⥤ Type (u + 1),
      (smallCrystallineProperty B.scheme B.ideal B.dividedPowers B.compatible
        B.ideal.subscheme (𝟙 B.ideal.subscheme)).ι.op.HasLeftKanExtension P] :
    MorphismOfTopoiIn
      (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
        B.ideal.subscheme (𝟙 B.ideal.subscheme) h_p₀)
      (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
        B.source B.sourceToClosed B.prime_nilpotent) :=
  MorphismOfTopoiIn.comp
    ((smallCrystallineProperty B.scheme B.ideal B.dividedPowers B.compatible
        B.ideal.subscheme (𝟙 B.ideal.subscheme)).ι.morphismOfTopoiInOfContinuous
      (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
        B.ideal.subscheme (𝟙 B.ideal.subscheme) h_p₀)
      (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
        B.ideal.subscheme (𝟙 B.ideal.subscheme)) :
      MorphismOfTopoiIn
        (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
          B.ideal.subscheme (𝟙 B.ideal.subscheme) h_p₀)
        (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
          B.ideal.subscheme (𝟙 B.ideal.subscheme)))
    ((closedSourceFunctor B.scheme B.ideal B.dividedPowers B.compatible
        B.source B.sourceToClosed).morphismOfTopoiInOfCocontinuous
      (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible B.toSpec
        B.source B.sourceToClosed B.prime_nilpotent)
      (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
        B.ideal.subscheme (𝟙 B.ideal.subscheme)))

end Base

end AlgebraicGeometry.Scheme.Crystalline

