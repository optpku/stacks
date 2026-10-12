/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReasLib.RingTheory.Valuation.Extension
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Valuative criterion for morphisms of algebraic spaces

A morphism of algebraic spaces satisfies the uniqueness part of the valuative
criterion when every solid valuative square has at most one lift, the existence
part when every such square admits a dominating extension of valuation rings
together with a lift of the extended square, and the valuative criterion when
both parts hold.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A valuative commutative square over a morphism `f : X ⟶ Y` of algebraic
spaces over `S` is a solid diagram `Spec(K) ⟶ X`, `Spec(R) ⟶ Y` with vertical
arrow `Spec(K) ⟶ Spec(R)`, where `R` is a valuation ring and `K` is a field of
fractions of `R`. -/
structure ValuativeCommSq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) where
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
  /-- The top map `Spec(K) ⟶ X` of algebraic spaces over `S`. -/
  i₁ : ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ structureHom)) ⟶ X
  /-- The bottom map `Spec(R) ⟶ Y` of algebraic spaces over `S`. -/
  i₂ : ofOver (Over.mk structureHom) ⟶ Y
  /-- The solid square commutes. -/
  commSq : CommSq i₁ (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl) f i₂

namespace ValuativeCommSq

attribute [instance] commRing domain valuationRing field algebra isFractionRing

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}

/-- Construct a valuative commutative square from a valuation ring, a field of
fractions, a structure morphism over `S`, and the two solid arrows. -/
def of (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] (K : Type u) [Field K]
    [Algebra R K] [IsFractionRing R K] (structureHom : Spec (.of R) ⟶ S)
    (i₁ : ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ structureHom)) ⟶ X)
    (i₂ : ofOver (Over.mk structureHom) ⟶ Y)
    (commSq : CommSq i₁ (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl) f i₂) :
    ValuativeCommSq f where
  R := R
  K := K
  structureHom := structureHom
  i₁ := i₁
  i₂ := i₂
  commSq := commSq

/-- `Spec(R)` as a scheme over `S`. -/
abbrev specR (sq : ValuativeCommSq f) : Over S := Over.mk sq.structureHom

/-- `Spec(K)` as a scheme over `S`, via the algebra map `R → K`. -/
abbrev specK (sq : ValuativeCommSq f) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom)

/-- The vertical morphism `Spec(K) ⟶ Spec(R)` of algebraic spaces over `S`. -/
abbrev verticalMap (sq : ValuativeCommSq f) : ofOver sq.specK ⟶ ofOver sq.specR :=
  ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))) rfl

/-- The vertical arrow is `ofOverHomMk` of `Spec.map` of the algebra map. -/
theorem verticalMap_eq (sq : ValuativeCommSq f) :
    sq.verticalMap = ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))) rfl :=
  sorry

/-- The two paths `Spec(K) ⟶ Y` of a solid valuative square agree. -/
theorem spec (sq : ValuativeCommSq f) : sq.i₁ ≫ f = sq.verticalMap ≫ sq.i₂ := sorry

/-- The structure morphism of `ValuativeCommSq.of` is the given morphism to `S`. -/
theorem of_structureHom (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] (K : Type u)
    [Field K] [Algebra R K] [IsFractionRing R K] (structureHom : Spec (.of R) ⟶ S)
    (i₁ : ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ structureHom)) ⟶ X)
    (i₂ : ofOver (Over.mk structureHom) ⟶ Y)
    (commSq : CommSq i₁ (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl) f i₂) :
    (of R K structureHom i₁ i₂ commSq).structureHom = structureHom :=
  sorry

/-- An extension of a valuative commutative square is a field extension `K'/K`,
a valuation ring `R'` of `K'` dominating `R`, and a morphism `Spec(R') ⟶ X`
filling the extended diagram. -/
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
  /-- The outer solid square after extending the valuation ring commutes. -/
  outerCommSq :
    CommSq
      (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.K K'))) specK_compat ≫ sq.i₁)
      (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) rfl) f
      (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R R'))) rfl ≫ sq.i₂)
  /-- A lift `Spec(R') ⟶ X` of the extended square. -/
  lift : outerCommSq.LiftStruct

namespace Extension

attribute [instance] commRing domain valuationRing field algebra_R algebra_K algebra algebra_base
  isFractionRing isExtension isScalarTower_K isScalarTower_R'

/-- The two structure morphisms `Spec(K') ⟶ S` obtained via `K` and via `R'` agree. -/
theorem specK_compat_of (sq : ValuativeCommSq f) (R' : Type u) [CommRing R'] [IsDomain R']
    [ValuationRing R'] (K' : Type u) [Field K'] [Algebra sq.R R'] [Algebra sq.K K']
    [Algebra R' K'] [Algebra sq.R K'] [IsFractionRing R' K']
    [IsExtensionOfValuationRings sq.R R'] [IsScalarTower sq.R sq.K K']
    [IsScalarTower sq.R R' K'] :
    Spec.map (CommRingCat.ofHom (algebraMap sq.K K')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom =
      Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom :=
  sorry

/-- Construct an extension of a valuative square from dominating valuation-ring
data and a morphism `Spec(R') ⟶ X` making both triangles of the extended
diagram commute. -/
def of (sq : ValuativeCommSq f) (R' : Type u) [CommRing R'] [IsDomain R'] [ValuationRing R']
    (K' : Type u) [Field K'] [Algebra sq.R R'] [Algebra sq.K K'] [Algebra R' K']
    [Algebra sq.R K'] [IsFractionRing R' K'] [IsExtensionOfValuationRings sq.R R']
    [IsScalarTower sq.R sq.K K'] [IsScalarTower sq.R R' K']
    (liftHom :
      ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom)) ⟶ X)
    (fac_left :
      ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) rfl ≫ liftHom =
        ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.K K')))
          (specK_compat_of sq R' K') ≫ sq.i₁)
    (fac_right :
      liftHom ≫ f =
        ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R R'))) rfl ≫ sq.i₂) :
    Extension sq where
  R' := R'
  K' := K'
  specK_compat := specK_compat_of sq R' K'
  outerCommSq := sorry
  lift := { l := liftHom, fac_left := fac_left, fac_right := fac_right }

/-- `Spec(R')` as a scheme over `S`, via the algebra map `R → R'`. -/
abbrev specR' {sq : ValuativeCommSq f} (e : Extension sq) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R e.R')) ≫ sq.structureHom)

/-- `Spec(K')` as a scheme over `S`, via the algebra map `R' → K'`. -/
abbrev specK' {sq : ValuativeCommSq f} (e : Extension sq) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap e.R' e.K')) ≫
    Spec.map (CommRingCat.ofHom (algebraMap sq.R e.R')) ≫ sq.structureHom)

/-- The morphism `Spec(R') ⟶ Spec(R)` of algebraic spaces over `S`. -/
abbrev toSpecR {sq : ValuativeCommSq f} (e : Extension sq) :
    ofOver e.specR' ⟶ ofOver sq.specR :=
  ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R e.R'))) rfl

/-- The morphism `Spec(K') ⟶ Spec(K)` of algebraic spaces over `S`. -/
abbrev toSpecK {sq : ValuativeCommSq f} (e : Extension sq) :
    ofOver e.specK' ⟶ ofOver sq.specK :=
  ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.K e.K'))) e.specK_compat

/-- The vertical morphism `Spec(K') ⟶ Spec(R')` of algebraic spaces over `S`. -/
abbrev verticalMap {sq : ValuativeCommSq f} (e : Extension sq) :
    ofOver e.specK' ⟶ ofOver e.specR' :=
  ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap e.R' e.K'))) rfl

/-- The morphism `Spec(R') ⟶ X` filling the extended valuative diagram. -/
def liftHom {sq : ValuativeCommSq f} (e : Extension sq) : ofOver e.specR' ⟶ X :=
  e.lift.l

/-- The morphism of `Extension.of` is the given lift `Spec(R') ⟶ X`. -/
theorem of_liftHom (sq : ValuativeCommSq f) (R' : Type u) [CommRing R'] [IsDomain R']
    [ValuationRing R'] (K' : Type u) [Field K'] [Algebra sq.R R'] [Algebra sq.K K']
    [Algebra R' K'] [Algebra sq.R K'] [IsFractionRing R' K']
    [IsExtensionOfValuationRings sq.R R'] [IsScalarTower sq.R sq.K K']
    [IsScalarTower sq.R R' K']
    (liftHom :
      ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom)) ⟶ X)
    (fac_left :
      ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) rfl ≫ liftHom =
        ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.K K')))
          (specK_compat_of sq R' K') ≫ sq.i₁)
    (fac_right :
      liftHom ≫ f =
        ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R R'))) rfl ≫ sq.i₂) :
    (of sq R' K' liftHom fac_left fac_right).liftHom = liftHom :=
  sorry

/-- The upper triangle of an extended valuative square commutes:
`Spec(K') ⟶ Spec(R') ⟶ X` equals `Spec(K') ⟶ Spec(K) ⟶ X`. -/
theorem fac_left {sq : ValuativeCommSq f} (e : Extension sq) :
    e.verticalMap ≫ e.liftHom = e.toSpecK ≫ sq.i₁ :=
  sorry

/-- The lower triangle of an extended valuative square commutes:
`Spec(R') ⟶ X ⟶ Y` equals `Spec(R') ⟶ Spec(R) ⟶ Y`. -/
theorem fac_right {sq : ValuativeCommSq f} (e : Extension sq) :
    e.liftHom ≫ f = e.toSpecR ≫ sq.i₂ :=
  sorry

end Extension

end ValuativeCommSq

/-- A morphism of algebraic spaces satisfies the uniqueness part of the valuative
criterion if every valuative commutative square has at most one lift. -/
@[mk_iff]
class ValuativeCriterion.Uniqueness {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every valuative square has at most one dotted lift. -/
  subsingleton_liftStruct : ∀ sq : ValuativeCommSq f, Subsingleton sq.commSq.LiftStruct

/-- A morphism of algebraic spaces satisfies the existence part of the valuative
criterion if every valuative commutative square admits a dominating extension
together with a lift of the extended square. -/
@[mk_iff]
class ValuativeCriterion.Existence {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every valuative square admits a dominating extension with a lift. -/
  nonempty_extension : ∀ sq : ValuativeCommSq f, Nonempty sq.Extension

/-- A morphism of algebraic spaces satisfies the valuative criterion if it
satisfies both the uniqueness and existence parts. -/
@[mk_iff]
class ValuativeCriterion {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop
    extends ValuativeCriterion.Uniqueness f, ValuativeCriterion.Existence f

namespace ValuativeCriterion.Uniqueness

/-- The identity morphism of an algebraic space satisfies the uniqueness part of
the valuative criterion. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Uniqueness (𝟙 X) := sorry

/-- A morphism satisfies uniqueness if and only if every valuative square has at
most one lift. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Uniqueness f ↔ ∀ sq : ValuativeCommSq f, Subsingleton sq.commSq.LiftStruct :=
  sorry

end ValuativeCriterion.Uniqueness

namespace ValuativeCriterion.Existence

/-- The identity morphism of an algebraic space satisfies the existence part of
the valuative criterion. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Existence (𝟙 X) := sorry

/-- A morphism satisfies existence if and only if every valuative square admits a
dominating extension with a lift. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Existence f ↔ ∀ sq : ValuativeCommSq f, Nonempty sq.Extension :=
  sorry

end ValuativeCriterion.Existence

namespace ValuativeCriterion

/-- The identity morphism of an algebraic space satisfies the valuative
criterion. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : ValuativeCriterion (𝟙 X) := sorry

/-- A morphism satisfies the valuative criterion if and only if it satisfies both
the uniqueness and existence parts. -/
theorem iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ValuativeCriterion f ↔ Uniqueness f ∧ Existence f :=
  sorry

end ValuativeCriterion

end AlgebraicGeometry.AlgebraicSpace
