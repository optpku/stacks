/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Object
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Covering
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Small
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.InducedTopology

@[expose] public section

open AlgebraicGeometry CategoryTheory MorphismProperty CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry
namespace Scheme
namespace Crystalline

/- The small crystalline site is the full subcategory of `RelativeCRIS` on crystalline
objects whose source over `X` is an open immersion. -/
/-- The object property selecting crystalline objects with open source over `X`. -/
abbrev smallCrystallineProperty
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) :
    ObjectProperty (RelativeCRIS S I γ h_compatible X x₀) :=
  fun T ↦ IsOpenImmersion T.1.source.hom

/-- The full small crystalline site `Cris(X/S)` of crystalline objects with open source. -/
abbrev smallCrystallineSite
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) :=
  (smallCrystallineProperty S I γ h_compatible X x₀).FullSubcategory

/-- The open source in `X.smallZariskiSite` underlying a small crystalline object. -/
def smallCrystallineSource
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (T : smallCrystallineSite S I γ h_compatible X x₀) : X.smallZariskiSite :=
  let c := T.obj.1
  let U := c.source
  Over.mk ⊤ U.hom T.property

/-- The induced morphism of open sources associated to a small crystalline morphism. -/
def smallCrystallineSourceMap
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    {T U : smallCrystallineSite S I γ h_compatible X x₀}
    (f : T ⟶ U) : smallCrystallineSource S I γ h_compatible X x₀ T ⟶
      smallCrystallineSource S I γ h_compatible X x₀ U :=
  let φ := f.hom.source
  Over.Hom.mk φ trivial

end Crystalline
end Scheme
end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Crystalline

variable (S : Scheme.{u}) (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)

/-- for a standard topology `τ`, a family of morphisms
of divided-power thickenings over `X/S` is a `τ`-covering when each source is
the pullback of the target source along the corresponding thickening map and
the thickening maps form a `τ`-covering family of schemes. -/
def CrystallineCovering (τ : AlgebraicGeometry.StandardTopology)
    {ι : Type v} {B : RelativeCRIS S I γ h_compatible X x₀}
    (family : ι → Over B) : Prop :=
  (∀ i : ι,
    IsPullback (family i).hom.source.left (family i).left.1.inclusion
      B.1.inclusion (family i).hom.thickening) ∧
    Presieve.ofArrows (fun i : ι ↦ (family i).left.1.thickening)
      (fun i : ι ↦ (family i).hom.thickening) ∈
        Scheme.precoverage (StandardTopology.Small.morphismProperty τ) B.1.thickening

/-- The crystalline covering predicate unfolds to its source-pullback and
scheme-covering components. -/
theorem crystallineCovering_iff (τ : AlgebraicGeometry.StandardTopology)
    {ι : Type v} {B : RelativeCRIS S I γ h_compatible X x₀}
    (family : ι → Over B) :
    CrystallineCovering S I γ h_compatible X x₀ τ family ↔
      (∀ i : ι,
        IsPullback (family i).hom.source.left (family i).left.1.inclusion
          B.1.inclusion (family i).hom.thickening) ∧
        Presieve.ofArrows (fun i : ι ↦ (family i).left.1.thickening)
          (fun i : ι ↦ (family i).hom.thickening) ∈
            Scheme.precoverage (StandardTopology.Small.morphismProperty τ) B.1.thickening :=
  Iff.rfl

/-- The source component of a crystalline covering forms the indicated pullback square. -/
theorem CrystallineCovering.source_pullback (τ : AlgebraicGeometry.StandardTopology)
    {ι : Type v} {B : RelativeCRIS S I γ h_compatible X x₀}
    {family : ι → Over B} (h : CrystallineCovering S I γ h_compatible X x₀ τ family)
    (i : ι) :
    IsPullback (family i).hom.source.left (family i).left.1.inclusion
      B.1.inclusion (family i).hom.thickening := h.1 i

/-- The thickening maps of a crystalline covering form a `τ`-covering family. -/
theorem CrystallineCovering.thickening_cover (τ : AlgebraicGeometry.StandardTopology)
    {ι : Type v} {B : RelativeCRIS S I γ h_compatible X x₀}
    {family : ι → Over B} (h : CrystallineCovering S I γ h_compatible X x₀ τ family) :
    Presieve.ofArrows (fun i : ι ↦ (family i).left.1.thickening)
      (fun i : ι ↦ (family i).hom.thickening) ∈
        Scheme.precoverage (StandardTopology.Small.morphismProperty τ) B.1.thickening := h.2

/-- The precoverage whose covering families are the crystalline Zariski
families of cartesian source squares and Zariski thickening covers. -/
def crystallineZariskiPrecoverage :
    Precoverage (RelativeCRIS S I γ h_compatible X x₀) :=
  { coverings := fun B ↦ {R | ∃ (ι : Type v) (family : ι → Over B),
      CrystallineCovering S I γ h_compatible X x₀ .zariski family ∧
        R = Presieve.ofArrows (fun i : ι ↦ (family i).left)
          (fun i : ι ↦ (family i).hom)} }

/-- A presieve belongs to the crystalline Zariski precoverage exactly when it is
represented by an indexed crystalline Zariski covering family. -/
theorem mem_crystallineZariskiPrecoverage_iff
    {B : RelativeCRIS S I γ h_compatible X x₀} {R : Presieve B} :
    R ∈ crystallineZariskiPrecoverage.{u, v} S I γ h_compatible X x₀ B ↔
      ∃ (ι : Type v) (family : ι → Over B),
        CrystallineCovering S I γ h_compatible X x₀ .zariski family ∧
          R = Presieve.ofArrows (fun i : ι ↦ (family i).left)
            (fun i : ι ↦ (family i).hom) := Iff.rfl

/-- the big crystalline site is the category `CRIS(X/S)`
endowed with the Grothendieck topology generated by the crystalline Zariski
covering families. -/
def crystallineZariskiTopology :
    GrothendieckTopology (RelativeCRIS S I γ h_compatible X x₀) :=
  (crystallineZariskiPrecoverage.{u, u} S I γ h_compatible X x₀).toGrothendieck

/-- The crystalline Zariski topology is the topology generated by the
explicit crystalline Zariski precoverage. -/
theorem crystallineZariskiTopology_def :
    crystallineZariskiTopology S I γ h_compatible X x₀ =
      (crystallineZariskiPrecoverage.{u, u} S I γ h_compatible X x₀).toGrothendieck := rfl

/-- the big crystalline topos is the category of sheaves
of types on `CRIS(X/S)` with its crystalline Zariski topology. -/
abbrev bigCrystallineTopos :=
  Sheaf (crystallineZariskiTopology S I γ h_compatible X x₀) (Type (u + 1))

/-- The big crystalline topos abbreviation unfolds to the sheaf category on
the crystalline Zariski site. -/
theorem bigCrystallineTopos_def :
    bigCrystallineTopos S I γ h_compatible X x₀ =
      Sheaf (crystallineZariskiTopology S I γ h_compatible X x₀) (Type (u + 1)) := rfl

end AlgebraicGeometry.Scheme.Crystalline

namespace AlgebraicGeometry.Scheme.Crystalline

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (S : Scheme.{u}) (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))


/-- Small crystalline coverings are open coverings of the thickenings with
the corresponding source squares cartesian. A map that only fixes the open
source is not thereby a cover. -/
def smallCrystallineZariskiPrecoverage :
    Precoverage (smallCrystallineSite S I γ h_compatible X x₀) :=
  { coverings := fun B ↦ {R | ∃ (ι : Type u) (family : ι → Over B),
      (∀ i : ι,
        IsPullback (family i).hom.hom.source.left (family i).left.obj.1.inclusion
          B.obj.1.inclusion (family i).hom.hom.thickening) ∧
      StandardCovering .zariski
        (fun i : ι ↦ (family i).left.obj.1.thickening)
        (fun i : ι ↦ (family i).hom.hom.thickening) ∧
      R = Presieve.ofArrows (fun i : ι ↦ (family i).left)
        (fun i : ι ↦ (family i).hom)} }

/-- the small crystalline site carries the topology
generated by actual Zariski covering families of thickenings. -/
def smallCrystallineTopology
    (p : ℕ) [Fact (Nat.Prime p)] (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible : ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) :
    GrothendieckTopology (smallCrystallineSite S I γ h_compatible X x₀) :=
  (smallCrystallineZariskiPrecoverage S I γ h_compatible X x₀).toGrothendieck

/-- The small crystalline topology is generated by its thickening covers. -/
theorem smallCrystallineTopology_def :
    smallCrystallineTopology p S I γ h_compatible s X x₀ h_p =
      (smallCrystallineZariskiPrecoverage S I γ h_compatible X x₀).toGrothendieck := rfl

/-- the crystalline topos is the category of sheaves of
types on the small crystalline site with its Zariski topology. -/
abbrev smallCrystallineTopos :=
  Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
    (Type (u + 1))

/-- The crystalline topos abbreviation unfolds to the sheaf category on the
small crystalline Zariski site. -/
theorem smallCrystallineTopos_def :
    smallCrystallineTopos p S I γ h_compatible s X x₀ h_p =
      Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
        (Type (u + 1)) := rfl

end AlgebraicGeometry.Scheme.Crystalline

namespace AlgebraicGeometry.Scheme.Crystalline

variable (S : Scheme.{u}) (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)

/-- The object property selecting small crystalline objects whose source over `X` is an
isomorphism, i.e. divided power thickenings of the form `(X, T, δ)`. -/
def isWholeSource :
    ObjectProperty (smallCrystallineSite S I γ h_compatible X x₀) :=
  fun T ↦ IsIso T.obj.1.source.hom

/-- Membership in `isWholeSource` is isomorphism of the source morphism over `X`. -/
theorem isWholeSource_iff
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    isWholeSource S I γ h_compatible X x₀ T ↔ IsIso T.obj.1.source.hom :=
  Iff.rfl

/-- The full subcategory of `Cris(X/S)` on whole-source objects `(X, T, δ)`. -/
abbrev chaoticSite :=
  (isWholeSource S I γ h_compatible X x₀).FullSubcategory

/-- The chaotic topology on the whole-source full subcategory of `Cris(X/S)`. -/
abbrev chaoticTopology :
    GrothendieckTopology (chaoticSite S I γ h_compatible X x₀) :=
  GrothendieckTopology.trivial _

/-- The chaotic topology on the whole-source site is the bottom Grothendieck topology. -/
theorem chaoticTopology_eq_bot :
    chaoticTopology S I γ h_compatible X x₀ =
      (⊥ : GrothendieckTopology (chaoticSite S I γ h_compatible X x₀)) :=
  rfl

/-- The fully faithful inclusion of the whole-source subcategory into `Cris(X/S)`. -/
def chaoticInclusion :
    chaoticSite S I γ h_compatible X x₀ ⥤
      smallCrystallineSite S I γ h_compatible X x₀ :=
  ObjectProperty.ι (isWholeSource S I γ h_compatible X x₀)

/-- The inclusion of a whole-source object recovers the underlying small crystalline object. -/
theorem chaoticInclusion_obj
    (T : chaoticSite S I γ h_compatible X x₀) :
    (chaoticInclusion S I γ h_compatible X x₀).obj T = T.obj :=
  rfl

end AlgebraicGeometry.Scheme.Crystalline

namespace AlgebraicGeometry.Scheme.Crystalline

variable {S : Scheme.{u}} {I : S.IdealSheafData}
variable {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible :
    ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

/-- The Grothendieck topology on `Cris(X/S)` induced from the big crystalline Zariski
topology. -/
def smallCrystallineZariskiTopology :
    GrothendieckTopology (smallCrystallineSite S I γ h_compatible X x₀) :=
  (smallCrystallineProperty S I γ h_compatible X x₀).ι.inducedTopology
    (crystallineZariskiTopology S I γ h_compatible X x₀)

/-- The induced small crystalline topology is the induced topology of the big
crystalline Zariski topology along the inclusion of `Cris(X/S)`. -/
theorem smallCrystallineZariskiTopology_def :
    smallCrystallineZariskiTopology (S := S) (I := I) (γ := γ)
        (h_compatible := h_compatible) (X := X) (x₀ := x₀) =
      (smallCrystallineProperty S I γ h_compatible X x₀).ι.inducedTopology
        (crystallineZariskiTopology S I γ h_compatible X x₀) :=
  rfl


end AlgebraicGeometry.Scheme.Crystalline

namespace AlgebraicGeometry.Scheme.Crystalline

variable {S : Scheme.{u}} {I : S.IdealSheafData}
  {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
  {h_compatible : ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
  {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

/-- Restriction along the identity inclusion of an open thickening is the identity morphism. -/
theorem relativeRestrictOpenHom_id (T : RelativeCRIS S I γ h_compatible X x₀)
    (U : T.1.thickening.Opens) :
    CrystallineObject.restrictOpenHom T.1 (le_refl U) =
      CrystallineObject.Hom.id (relativeRestrictOpen T U).1 := sorry

/-- Restriction along a composite inclusion of opens is the composite of the restriction maps. -/
theorem relativeRestrictOpenHom_comp (T : RelativeCRIS S I γ h_compatible X x₀)
    {U V W : T.1.thickening.Opens} (h : U ≤ V) (k : V ≤ W) :
    CrystallineObject.restrictOpenHom T.1 (le_trans h k) =
      CrystallineObject.Hom.comp (CrystallineObject.restrictOpenHom T.1 h)
        (CrystallineObject.restrictOpenHom T.1 k) := sorry

/-- Restricting a small crystalline object to an open thickening preserves its open source. -/
theorem relativeRestrictOpen_source_isOpenImmersion
    (T : smallCrystallineSite S I γ h_compatible X x₀) (U : T.obj.1.thickening.Opens) :
    IsOpenImmersion (relativeRestrictOpen T.obj U).1.source.hom := sorry

/-- The open subsets of a thickening form a diagram of relative crystalline objects. -/
noncomputable def relativeOpensFunctor (T : RelativeCRIS S I γ h_compatible X x₀) :
    T.1.thickening.Opens ⥤ RelativeCRIS S I γ h_compatible X x₀ where
  obj U := relativeRestrictOpen T U
  map h := CrystallineObject.restrictOpenHom T.1 h.le
  map_id U := relativeRestrictOpenHom_id T U
  map_comp h k := relativeRestrictOpenHom_comp T h.le k.le

/-- Open restriction of a small crystalline object stays in the small crystalline site. -/
noncomputable def smallOpensFunctor (T : smallCrystallineSite S I γ h_compatible X x₀) :
    T.obj.1.thickening.Opens ⥤ smallCrystallineSite S I γ h_compatible X x₀ :=
  ObjectProperty.lift (smallCrystallineProperty S I γ h_compatible X x₀)
    (relativeOpensFunctor T.obj) (relativeRestrictOpen_source_isOpenImmersion T)

variable (S I γ h_compatible X x₀)

/-- Underlying thickening morphism of a morphism of small crystalline objects. -/
def smallCrystallineHom_thickening
    {T U : smallCrystallineSite S I γ h_compatible X x₀} (f : T ⟶ U) :=
  f.hom.thickening

/-- The thickening morphism of a small crystalline morphism is the hom-component thickening. -/
theorem smallCrystallineHom_thickening_eq
    {T U : smallCrystallineSite S I γ h_compatible X x₀} (f : T ⟶ U) :
    smallCrystallineHom_thickening S I γ h_compatible X x₀ f = f.hom.thickening :=
  rfl


end AlgebraicGeometry.Scheme.Crystalline
