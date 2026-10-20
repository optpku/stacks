/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Construction
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.RingTheory.Valuation.Extension
public import stacks_project.Chap110.Lemma_110_53_1

/-!
# Existence part of the valuative criterion at Picard Hom-universe

A 1-morphism of categories fibred in groupoids over `Over S`, in the
Hom-universe of `picardStack` and `Classifying.toGroupoids`, satisfies the
existence part of the valuative criterion when every solid 2-commutative
valuative square admits a dominating extension of valuation rings together
with a dotted arrow of the induced outer rectangle, matching Morphisms of
Stacks, Definition 101.39.10.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}}

/-- The 1-morphism of Hom-universe `u + 1` slice fibrations induced by a
morphism of schemes over `S`. -/
def sliceHom {U V : Over S} (f : U ⟶ V) :
    Classifying.slice U ⟶ Classifying.slice V :=
  ofBasedFunctor
    { toFunctor :=
        (ULiftHom.down : ULiftHom.{u + 1} (Over U) ⥤ Over U) ⋙
          Over.map f ⋙
          (ULiftHom.up : Over V ⥤ ULiftHom.{u + 1} (Over V))
      w := sorry }

/-- The total functor of `sliceHom f` is the universe lift of `Over.map f`. -/
theorem sliceHom_toFunctor {U V : Over S} (f : U ⟶ V) :
    toFunctor (sliceHom f) =
      (ULiftHom.down : ULiftHom.{u + 1} (Over U) ⥤ Over U) ⋙
        Over.map f ⋙
        (ULiftHom.up : Over V ⥤ ULiftHom.{u + 1} (Over V)) :=
  sorry

/-- The identity morphism of a scheme over `S` induces the identity 1-morphism
of slice fibrations. -/
theorem sliceHom_id (U : Over S) : sliceHom (𝟙 U) = 𝟙 (Classifying.slice U) :=
  sorry

/-- The 1-morphism of slice fibrations induced by a morphism of schemes
compatible with given structure morphisms to `S`. -/
def sliceHomMk {XK XL : Scheme.{u}} {σK : XK ⟶ S} {σL : XL ⟶ S}
    (g : XK ⟶ XL) (hg : g ≫ σL = σK) :
    Classifying.slice (Over.mk σK) ⟶ Classifying.slice (Over.mk σL) :=
  sliceHom (Over.homMk g hg)

/-- `sliceHomMk g hg` is `sliceHom` of the corresponding morphism in `Over S`. -/
theorem sliceHomMk_eq {XK XL : Scheme.{u}} {σK : XK ⟶ S} {σL : XL ⟶ S}
    (g : XK ⟶ XL) (hg : g ≫ σL = σK) :
    sliceHomMk g hg = sliceHom (Over.homMk g hg) :=
  sorry

/-- A valuative commutative square over a 1-morphism `f : X ⟶ Y` in the
Hom-universe of `Classifying.toGroupoids` is a solid 2-commutative diagram
`Spec(K) ⟶ X`, `Spec(R) ⟶ Y` with vertical arrow `Spec(K) ⟶ Spec(R)`, where
`R` is a valuation ring and `K` is a field of fractions of `R`. -/
structure ValuativeCommSq
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) where
  /-- The valuation ring of a valuative commutative square. -/
  R : Type u
  [commRing : CommRing R]
  [domain : IsDomain R]
  [valuationRing : ValuationRing R]
  /-- The field of fractions of a valuative commutative square. -/
  K : Type u
  [field : Field K]
  [algebra : Algebra R K]
  [isFractionRing : IsFractionRing R K]
  /-- The structure morphism of `Spec(R)` over `S`. -/
  structureHom : Spec (.of R) ⟶ S
  /-- The top map `Spec(K) ⟶ X` of groupoid fibrations over `S`. -/
  i₁ :
    Classifying.slice
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ structureHom)) ⟶
      X
  /-- The bottom map `Spec(R) ⟶ Y` of groupoid fibrations over `S`. -/
  i₂ : Classifying.slice (Over.mk structureHom) ⟶ Y
  /-- The 2-cell `j ≫ y ≅ x ≫ f` witnessing 2-commutativity of the solid square. -/
  iso :
    sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl ≫ i₂ ≅
      i₁ ≫ f

namespace ValuativeCommSq

attribute [instance] commRing domain valuationRing field algebra isFractionRing

variable {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
variable {f : X ⟶ Y}

/-- Construct a valuative commutative square from a valuation ring, a field of
fractions, a structure morphism over `S`, the two solid arrows, and a 2-cell. -/
def of (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] (K : Type u)
    [Field K] [Algebra R K] [IsFractionRing R K]
    (structureHom : Spec (.of R) ⟶ S)
    (i₁ :
      Classifying.slice
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ structureHom)) ⟶
        X)
    (i₂ : Classifying.slice (Over.mk structureHom) ⟶ Y)
    (iso :
      sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl ≫ i₂ ≅
        i₁ ≫ f) :
    ValuativeCommSq f where
  R := R
  K := K
  structureHom := structureHom
  i₁ := i₁
  i₂ := i₂
  iso := iso

/-- The valuation ring of `ValuativeCommSq.of` is the given ring. -/
theorem of_R (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] (K : Type u)
    [Field K] [Algebra R K] [IsFractionRing R K]
    (structureHom : Spec (.of R) ⟶ S)
    (i₁ :
      Classifying.slice
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ structureHom)) ⟶
        X)
    (i₂ : Classifying.slice (Over.mk structureHom) ⟶ Y)
    (iso :
      sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl ≫ i₂ ≅
        i₁ ≫ f) :
    (of R K structureHom i₁ i₂ iso).R = R :=
  sorry

/-- `Spec(R)` as a scheme over `S`. -/
abbrev specR (sq : ValuativeCommSq f) : Over S := Over.mk sq.structureHom

/-- `specR` is `Over.mk` of the structure morphism of `Spec(R)`. -/
theorem specR_eq (sq : ValuativeCommSq f) : sq.specR = Over.mk sq.structureHom :=
  sorry

/-- `Spec(K)` as a scheme over `S`, via the algebra map `R → K`. -/
abbrev specK (sq : ValuativeCommSq f) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom)

/-- `specK` is `Over.mk` of the structure morphism of `Spec(K)`. -/
theorem specK_eq (sq : ValuativeCommSq f) :
    sq.specK =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom) :=
  sorry

/-- The vertical morphism `Spec(K) ⟶ Spec(R)` of groupoid fibrations over `S`. -/
abbrev verticalMap (sq : ValuativeCommSq f) :
    Classifying.slice sq.specK ⟶ Classifying.slice sq.specR :=
  sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))) rfl

/-- The vertical arrow is `sliceHomMk` of `Spec.map` of the algebra map. -/
theorem verticalMap_eq (sq : ValuativeCommSq f) :
    sq.verticalMap =
      sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))) rfl :=
  sorry

/-- The 2-cell `j ≫ y ≅ x ≫ f` of a solid valuative square. -/
def two_commute (sq : ValuativeCommSq f) :
    sq.verticalMap ≫ sq.i₂ ≅ sq.i₁ ≫ f :=
  sq.iso

/-- `two_commute` is the stored 2-cell of the valuative square. -/
theorem two_commute_eq (sq : ValuativeCommSq f) : two_commute sq = sq.iso :=
  sorry

/-- The solid valuative square, viewed as a 2-commutative cospan cone. -/
def toCone (sq : ValuativeCommSq f) : Bicategory.PseudoPullbackCone sq.i₂ f where
  pt := Classifying.slice sq.specK
  fst := sq.verticalMap
  snd := sq.i₁
  iso := sq.iso

/-- The apex of `toCone` is the slice of `Spec(K)`. -/
theorem toCone_pt (sq : ValuativeCommSq f) :
    sq.toCone.pt = Classifying.slice sq.specK :=
  sorry

/-- The two structure morphisms `Spec(K') ⟶ S` obtained via `K` and via `R'`
agree. -/
theorem specK_compat_of (sq : ValuativeCommSq f) (R' : Type u) [CommRing R']
    [IsDomain R'] [ValuationRing R'] (K' : Type u) [Field K'] [Algebra sq.R R']
    [Algebra sq.K K'] [Algebra R' K'] [Algebra sq.R K'] [IsFractionRing R' K']
    [IsExtensionOfValuationRings sq.R R'] [IsScalarTower sq.R sq.K K']
    [IsScalarTower sq.R R' K'] :
    Spec.map (CommRingCat.ofHom (algebraMap sq.K K')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom =
      Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom :=
  sorry

/-- The two paths `Spec(K') ⟶ Spec(R)` of an extended valuative square agree. -/
theorem verticalMap_comp_toSpecR_of (sq : ValuativeCommSq f) (R' : Type u)
    [CommRing R'] [IsDomain R'] [ValuationRing R'] (K' : Type u) [Field K']
    [Algebra sq.R R'] [Algebra sq.K K'] [Algebra R' K'] [Algebra sq.R K']
    [IsFractionRing R' K'] [IsExtensionOfValuationRings sq.R R']
    [IsScalarTower sq.R sq.K K'] [IsScalarTower sq.R R' K']
    (specK_compat :
      Spec.map (CommRingCat.ofHom (algebraMap sq.K K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom =
        Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom) :
    sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) rfl ≫
        sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R R'))) rfl =
      sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.K K'))) specK_compat ≫
        sq.verticalMap :=
  sorry

/-- The induced outer 2-cell of an extended valuative rectangle, obtained by
whiskering the original 2-cell along `Spec(K') ⟶ Spec(K)` and reassociating
along the commuting Spec square. -/
def inducedOuterIso (sq : ValuativeCommSq f) (R' : Type u) [CommRing R']
    [IsDomain R'] [ValuationRing R'] (K' : Type u) [Field K'] [Algebra sq.R R']
    [Algebra sq.K K'] [Algebra R' K'] [Algebra sq.R K'] [IsFractionRing R' K']
    [IsExtensionOfValuationRings sq.R R'] [IsScalarTower sq.R sq.K K']
    [IsScalarTower sq.R R' K']
    (specK_compat :
      Spec.map (CommRingCat.ofHom (algebraMap sq.K K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom =
        Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom) :
    sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) rfl ≫
        (sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R R'))) rfl ≫ sq.i₂) ≅
      (sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.K K'))) specK_compat ≫
          sq.i₁) ≫
        f :=
  let j' := sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) rfl
  let toSpecR := sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R R'))) rfl
  let toSpecK :=
    sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.K K'))) specK_compat
  (α_ j' toSpecR sq.i₂).symm ≪≫
    eqToIso (verticalMap_comp_toSpecR_of sq R' K' specK_compat) ▷ᵢ sq.i₂ ≪≫
    α_ toSpecK sq.verticalMap sq.i₂ ≪≫
    toSpecK ◁ᵢ sq.iso ≪≫
    (α_ toSpecK sq.i₁ f).symm

/-- The solid outer rectangle of an extended valuative square, as a
2-commutative cospan cone whose 2-cell is the induced whiskering of the
original 2-cell. -/
def inducedOuterCone (sq : ValuativeCommSq f) (R' : Type u) [CommRing R']
    [IsDomain R'] [ValuationRing R'] (K' : Type u) [Field K'] [Algebra sq.R R']
    [Algebra sq.K K'] [Algebra R' K'] [Algebra sq.R K'] [IsFractionRing R' K']
    [IsExtensionOfValuationRings sq.R R'] [IsScalarTower sq.R sq.K K']
    [IsScalarTower sq.R R' K']
    (specK_compat :
      Spec.map (CommRingCat.ofHom (algebraMap sq.K K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom =
        Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom) :
    Bicategory.PseudoPullbackCone
      (sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R R'))) rfl ≫ sq.i₂) f where
  pt :=
    Classifying.slice
      (Over.mk
        (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom))
  fst := sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) rfl
  snd :=
    sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.K K'))) specK_compat ≫ sq.i₁
  iso := inducedOuterIso sq R' K' specK_compat

/-- The 2-cell of `inducedOuterCone` is the induced whiskering `inducedOuterIso`. -/
theorem inducedOuterCone_iso (sq : ValuativeCommSq f) (R' : Type u) [CommRing R']
    [IsDomain R'] [ValuationRing R'] (K' : Type u) [Field K'] [Algebra sq.R R']
    [Algebra sq.K K'] [Algebra R' K'] [Algebra sq.R K'] [IsFractionRing R' K']
    [IsExtensionOfValuationRings sq.R R'] [IsScalarTower sq.R sq.K K']
    [IsScalarTower sq.R R' K']
    (specK_compat :
      Spec.map (CommRingCat.ofHom (algebraMap sq.K K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom =
        Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom) :
    (inducedOuterCone sq R' K' specK_compat).iso =
      inducedOuterIso sq R' K' specK_compat :=
  sorry

/-- An extension of a valuative commutative square is a field extension `K'/K`,
a valuation ring `R'` of `K'` dominating `R`, and a dotted arrow filling the
induced outer rectangle. -/
structure Extension (sq : ValuativeCommSq f) where
  /-- The dominating valuation ring. -/
  R' : Type u
  [commRing : CommRing R']
  [domain : IsDomain R']
  [valuationRing : ValuationRing R']
  /-- The extended field of fractions. -/
  K' : Type u
  [field : Field K']
  [algebra_R : Algebra sq.R R']
  [algebra_K : Algebra sq.K K']
  [algebra : Algebra R' K']
  [algebra_base : Algebra sq.R K']
  [isFractionRing : IsFractionRing R' K']
  [isExtension : IsExtensionOfValuationRings sq.R R']
  [isScalarTower_K : IsScalarTower sq.R sq.K K']
  [isScalarTower_R' : IsScalarTower sq.R R' K']
  /-- The two structure morphisms of `Spec(K')` over `S` agree. -/
  specK_compat :
    Spec.map (CommRingCat.ofHom (algebraMap sq.K K')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom =
      Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom
  /-- A dotted arrow of the induced outer rectangle. -/
  lift : DottedArrow (inducedOuterCone sq R' K' specK_compat)

namespace Extension

attribute [instance] commRing domain valuationRing field algebra_R algebra_K algebra
  algebra_base isFractionRing isExtension isScalarTower_K isScalarTower_R'

/-- `Spec(R')` as a scheme over `S`, via the algebra map `R → R'`. -/
abbrev specR' {sq : ValuativeCommSq f} (e : Extension sq) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R e.R')) ≫ sq.structureHom)

/-- `specR'` is `Over.mk` of the structure morphism of `Spec(R')`. -/
theorem specR'_eq {sq : ValuativeCommSq f} (e : Extension sq) :
    e.specR' =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R e.R')) ≫ sq.structureHom) :=
  sorry

/-- `Spec(K')` as a scheme over `S`, via the algebra map `R' → K'`. -/
abbrev specK' {sq : ValuativeCommSq f} (e : Extension sq) : Over S :=
  Over.mk
    (Spec.map (CommRingCat.ofHom (algebraMap e.R' e.K')) ≫
      Spec.map (CommRingCat.ofHom (algebraMap sq.R e.R')) ≫ sq.structureHom)

/-- `specK'` is `Over.mk` of the structure morphism of `Spec(K')` via `R'`. -/
theorem specK'_eq {sq : ValuativeCommSq f} (e : Extension sq) :
    e.specK' =
      Over.mk
        (Spec.map (CommRingCat.ofHom (algebraMap e.R' e.K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R e.R')) ≫ sq.structureHom) :=
  sorry

/-- Construct an extension of a valuative square from dominating valuation-ring
data and a dotted arrow of the induced outer cone. -/
def of (sq : ValuativeCommSq f) (R' : Type u) [CommRing R'] [IsDomain R']
    [ValuationRing R'] (K' : Type u) [Field K'] [Algebra sq.R R'] [Algebra sq.K K']
    [Algebra R' K'] [Algebra sq.R K'] [IsFractionRing R' K']
    [IsExtensionOfValuationRings sq.R R'] [IsScalarTower sq.R sq.K K']
    [IsScalarTower sq.R R' K']
    (lift : DottedArrow (inducedOuterCone sq R' K' (specK_compat_of sq R' K'))) :
    Extension sq where
  R' := R'
  K' := K'
  specK_compat := specK_compat_of sq R' K'
  lift := lift

/-- The dominating valuation ring of `Extension.of` is the given ring. -/
theorem of_R' (sq : ValuativeCommSq f) (R' : Type u) [CommRing R'] [IsDomain R']
    [ValuationRing R'] (K' : Type u) [Field K'] [Algebra sq.R R'] [Algebra sq.K K']
    [Algebra R' K'] [Algebra sq.R K'] [IsFractionRing R' K']
    [IsExtensionOfValuationRings sq.R R'] [IsScalarTower sq.R sq.K K']
    [IsScalarTower sq.R R' K']
    (lift : DottedArrow (inducedOuterCone sq R' K' (specK_compat_of sq R' K'))) :
    (of sq R' K' lift).R' = R' :=
  sorry

/-- The dotted morphism `Spec(R') ⟶ X` filling the extended valuative diagram. -/
abbrev liftArrow {sq : ValuativeCommSq f} (e : Extension sq) :
    Classifying.slice e.specR' ⟶ X :=
  e.lift.arrow

/-- `liftArrow` is the dotted 1-morphism of the stored dotted arrow. -/
theorem liftArrow_eq {sq : ValuativeCommSq f} (e : Extension sq) :
    e.liftArrow = e.lift.arrow :=
  sorry

end Extension

end ValuativeCommSq

/-- A 1-morphism of groupoid fibrations in the Hom-universe of
`Classifying.toGroupoids` satisfies the existence part of the valuative
criterion if every valuative commutative square admits a dominating extension
together with a dotted arrow of the extended rectangle. -/
@[mk_iff]
class ValuativeCriterion.Existence
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) : Prop where
  /-- Every valuative square admits a dominating extension with a dotted arrow. -/
  nonempty_extension : ∀ sq : ValuativeCommSq f, Nonempty sq.Extension

namespace ValuativeCriterion.Existence

/-- The identity 1-morphism of a groupoid fibration satisfies the existence part
of the valuative criterion. -/
instance id {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)} :
    Existence (𝟙 X) :=
  sorry

/-- A 1-morphism satisfies existence if and only if every valuative square admits
a dominating extension with a dotted arrow. -/
theorem spec {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) :
    Existence f ↔ ∀ sq : ValuativeCommSq f, Nonempty sq.Extension :=
  sorry

end ValuativeCriterion.Existence

end AlgebraicGeometry.AlgebraicSpace.Picard
