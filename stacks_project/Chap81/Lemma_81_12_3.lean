/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Maps
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap81.Lemma_81_12_2_Affine

/-!
# Lemma 81.12.3

For a Beauville–Laszlo glueing pair, the equivalence of Lemma 81.12.2 identifies
morphisms of affine glueable algebraic spaces over `X = space R` having one of
the properties finite, closed immersion, flat, finite type, flat and finite
presentation, or étale with morphisms of affine triples whose components have
the same property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing

/-- The six morphism properties finite, closed immersion, flat, finite type,
flat and of finite presentation, and étale. -/
inductive AffineMorphismKind : Type where
  /-- Finite morphisms of algebraic spaces. -/
  | finite
  /-- Closed immersions of algebraic spaces. -/
  | closedImmersion
  /-- Flat morphisms of algebraic spaces. -/
  | flat
  /-- Finite type morphisms of algebraic spaces. -/
  | finiteType
  /-- Morphisms that are flat and of finite presentation. -/
  | flatFinitePresentation
  /-- Étale morphisms of algebraic spaces. -/
  | etale

namespace AffineMorphismKind

/-- The algebraic-space morphism property associated to an affine morphism kind. -/
def property (P : AffineMorphismKind) {S : Scheme.{u}} :
    MorphismProperty (AlgebraicSpace S) :=
  match P with
  | .finite => (@AlgebraicSpace.IsFinite S : MorphismProperty (AlgebraicSpace S))
  | .closedImmersion =>
      (@AlgebraicSpace.IsClosedImmersion S : MorphismProperty (AlgebraicSpace S))
  | .flat => (@AlgebraicSpace.Flat S : MorphismProperty (AlgebraicSpace S))
  | .finiteType => (@AlgebraicSpace.FiniteType S : MorphismProperty (AlgebraicSpace S))
  | .flatFinitePresentation =>
      ((@AlgebraicSpace.Flat S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@AlgebraicSpace.FinitePresentation S : MorphismProperty (AlgebraicSpace S)))
  | .etale => (@AlgebraicSpace.Etale S : MorphismProperty (AlgebraicSpace S))

/-- `finite.property` is the finite morphism property of algebraic spaces. -/
theorem property_finite {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : X ⟶ Y) :
    property .finite φ ↔ AlgebraicSpace.IsFinite φ :=
  sorry

/-- `closedImmersion.property` is the closed-immersion property of algebraic spaces. -/
theorem property_closedImmersion {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : X ⟶ Y) :
    property .closedImmersion φ ↔ AlgebraicSpace.IsClosedImmersion φ :=
  sorry

/-- `flat.property` is the flat morphism property of algebraic spaces. -/
theorem property_flat {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : X ⟶ Y) :
    property .flat φ ↔ AlgebraicSpace.Flat φ :=
  sorry

/-- `finiteType.property` is the finite-type morphism property of algebraic spaces. -/
theorem property_finiteType {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : X ⟶ Y) :
    property .finiteType φ ↔ AlgebraicSpace.FiniteType φ :=
  sorry

/-- `flatFinitePresentation.property` is the infimum of flat and finite presentation. -/
theorem property_flatFinitePresentation {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (φ : X ⟶ Y) :
    property .flatFinitePresentation φ ↔
      ((@AlgebraicSpace.Flat S : MorphismProperty (AlgebraicSpace S)) ⊓
          (@AlgebraicSpace.FinitePresentation S : MorphismProperty (AlgebraicSpace S)))
        φ :=
  sorry

/-- A morphism has `flatFinitePresentation.property` iff it is flat and of finite
presentation. -/
theorem property_flatFinitePresentation_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (φ : X ⟶ Y) :
    property .flatFinitePresentation φ ↔
      AlgebraicSpace.Flat φ ∧ AlgebraicSpace.FinitePresentation φ :=
  sorry

/-- `etale.property` is the étale morphism property of algebraic spaces. -/
theorem property_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : X ⟶ Y) :
    property .etale φ ↔ AlgebraicSpace.Etale φ :=
  sorry

/-- The ring-homomorphism property associated to an affine morphism kind. -/
def ringHom (P : AffineMorphismKind) {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) : Prop :=
  match P with
  | .finite => φ.Finite
  | .closedImmersion => Function.Surjective φ
  | .flat => φ.Flat
  | .finiteType => φ.FiniteType
  | .flatFinitePresentation => φ.Flat ∧ φ.FinitePresentation
  | .etale => φ.Etale

/-- `closedImmersion.ringHom` is surjectivity of a ring homomorphism. -/
theorem ringHom_closedImmersion {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    ringHom .closedImmersion φ ↔ Function.Surjective φ :=
  sorry

/-- A ring homomorphism has `flatFinitePresentation.ringHom` iff it is flat and of
finite presentation. -/
theorem ringHom_flatFinitePresentation_iff {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) :
    ringHom .flatFinitePresentation φ ↔ φ.Flat ∧ φ.FinitePresentation :=
  sorry

end AffineMorphismKind

/-- The overlap component of a morphism of triples in `Spaces(U ← U' → X')`. -/
def overlapMap {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] {f : R}
    {X Y : category R' f} (g : X ⟶ Y) : overlap X ⟶ overlap Y :=
  (Over.pullback (restrict R' f)).map g.fst

/-- `overlapMap g` is the image of `g.fst` under pullback along `restrict R' f`. -/
theorem overlapMap_eq {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] {f : R}
    {X Y : category R' f} (g : X ⟶ Y) :
    overlapMap g = (Over.pullback (restrict R' f)).map g.fst :=
  sorry

/-- Lemma 81.12.3: let `(algebraMap R R', f)` be a glueing pair, and let `P` be one of
the properties finite, closed immersion, flat, finite type, flat and finite
presentation, or étale. Under the equivalence of Lemma 81.12.2, a morphism of
affine glueable algebraic spaces over `X = space R` has `P` if and only if the
three components of its image in `Spaces(U ← U' → X')` have `P`. -/
@[stacks 0F9R]
theorem functor_map_property_iff {R R' : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f]
    (P : AffineMorphismKind) {Y Z : Over (space R)}
    (hY : affineGlueableProperty R' f Y) (hZ : affineGlueableProperty R' f Z)
    (α : Y ⟶ Z) :
    P.property α.left ↔
      P.property ((functor R' f).map α).fst.left ∧
        P.property (overlapMap ((functor R' f).map α)).left ∧
        P.property ((functor R' f).map α).snd.left :=
  sorry

/-- On morphisms of affine glueable spaces, the three-component form of
`functor_map_property_iff` is equivalent to the conjunction of the `fst` and
`snd` components. -/
theorem functor_map_property_fst_snd_iff {R R' : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f]
    (P : AffineMorphismKind) {Y Z : Over (space R)}
    (hY : affineGlueableProperty R' f Y) (hZ : affineGlueableProperty R' f Z)
    (α : Y ⟶ Z) :
    P.property ((functor R' f).map α).fst.left ∧
        P.property (overlapMap ((functor R' f).map α)).left ∧
        P.property ((functor R' f).map α).snd.left ↔
      P.property ((functor R' f).map α).fst.left ∧
        P.property ((functor R' f).map α).snd.left :=
  sorry

/-- The correspondence of `functor_map_property_iff`, stated on the full
subcategory of affine glueable algebraic spaces. -/
theorem affineGlueableFunctor_map_property_iff {R R' : Type u} [CommRing R]
    [CommRing R'] [Algebra R R'] (f : R)
    [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f] (P : AffineMorphismKind)
    {Y Z : (affineGlueableProperty R' f).FullSubcategory} (α : Y ⟶ Z) :
    P.property ((affineGlueableProperty R' f).ι.map α).left ↔
      P.property ((affineTripleProperty R' f).ι.map
          ((affineGlueableFunctor R' f).map α)).fst.left ∧
        P.property (overlapMap ((affineTripleProperty R' f).ι.map
          ((affineGlueableFunctor R' f).map α))).left ∧
        P.property ((affineTripleProperty R' f).ι.map
          ((affineGlueableFunctor R' f).map α)).snd.left :=
  sorry

/-- If `A → B` is an `R`-algebra homomorphism and `A`, `B` are glueable for
`(algebraMap R R', f)`, then `algebraMap A B` has the ring-homomorphism property
associated to `P` if and only if the induced maps `A_f → B_f` and
`R' ⊗[R] A → R' ⊗[R] B` do. -/
theorem algebraHom_property_iff {R R' A B : Type u} [CommRing R] [CommRing R']
    [CommRing A] [CommRing B] [Algebra R R'] [Algebra R A] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] (f : R)
    [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f] (P : AffineMorphismKind)
    (hA : (beauvilleLaszloModuleCechSequence R' A f).ShortExact)
    (hB : (beauvilleLaszloModuleCechSequence R' B f).ShortExact) :
    P.ringHom (algebraMap A B) ↔
      P.ringHom (Localization.awayMap (algebraMap A B) (algebraMap R A f)) ∧
        P.ringHom
          (Algebra.TensorProduct.map (AlgHom.id R R')
            (IsScalarTower.toAlgHom R A B)).toRingHom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing
