/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import stacks_project.Chap92.Lemma_92_4_1_PolynomialOver

/-!
# The triple polynomial site `C_{C/B/A}`

Objects are pairs of algebra maps `(P ⟶ B, Q ⟶ C)` with `P` a polynomial `A`-algebra and
`Q` a polynomial `P`-algebra. The opposite category is the site `C_{C/B/A}`. The three
forgetful/tensor functors are the covariant forms of `u1`, `u2`, and `u3`.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped TensorProduct

noncomputable section

universe u

namespace RingedSite.Cotangent

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- The `P`-algebra structure on `C` induced by an algebra map `P ⟶ B`. -/
@[reducible] def algebraPCOf {P : Type u} [CommRing P] [Algebra A P]
    (toB : P →ₐ[A] B) : Algebra P C :=
  RingHom.toAlgebra ((algebraMap B C).comp toB.toRingHom)

/-- Unfolding `algebraPCOf` recovers the composite algebra `P ⟶ B ⟶ C`. -/
theorem algebraPCOf_eq {P : Type u} [CommRing P] [Algebra A P] (toB : P →ₐ[A] B) :
    algebraPCOf toB = RingHom.toAlgebra ((algebraMap B C).comp toB.toRingHom) := sorry

/-- An object of the covariant category of pairs `(P ⟶ B, Q ⟶ C)` with `P` a polynomial
`A`-algebra and `Q` a polynomial `P`-algebra. The opposite of this category is the site
`C_{C/B/A}`. -/
structure PolynomialTriple (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] where
  /-- The source ring `P` of the first algebra map. -/
  P : Type u
  /-- Commutative ring structure on `P`. -/
  commRingP : CommRing P
  /-- The `A`-algebra structure on `P`. -/
  algebraAP : Algebra A P
  /-- The source ring `Q` of the second algebra map. -/
  Q : Type u
  /-- Commutative ring structure on `Q`. -/
  commRingQ : CommRing Q
  /-- The `P`-algebra structure on `Q`. -/
  algebraPQ : Algebra P Q
  /-- `P` is a polynomial `A`-algebra. -/
  isPolynomialP : Algebra.IsPolynomial A P
  /-- `Q` is a polynomial `P`-algebra. -/
  isPolynomialQ : Algebra.IsPolynomial P Q
  /-- The `A`-algebra map `P ⟶ B`. -/
  toB : P →ₐ[A] B
  /-- The `P`-algebra map `Q ⟶ C` over the composite `P ⟶ B ⟶ C`. -/
  toC : @AlgHom P Q C _ _ _ algebraPQ (algebraPCOf toB)

attribute [instance] PolynomialTriple.commRingP PolynomialTriple.commRingQ
  PolynomialTriple.algebraAP PolynomialTriple.algebraPQ
  PolynomialTriple.isPolynomialP PolynomialTriple.isPolynomialQ

namespace PolynomialTriple

variable (A B C) in
/-- Package a pair of polynomial algebra maps `(P ⟶ B, Q ⟶ C)` as a triple. -/
def of {P Q : Type u} [CommRing P] [CommRing Q]
    [Algebra A P] [Algebra P Q]
    [Algebra.IsPolynomial A P] [Algebra.IsPolynomial P Q]
    (toB : P →ₐ[A] B)
    (toC : @AlgHom P Q C _ _ _ _ (algebraPCOf toB)) : PolynomialTriple A B C where
  P := P
  commRingP := inferInstance
  algebraAP := inferInstance
  Q := Q
  commRingQ := inferInstance
  algebraPQ := inferInstance
  isPolynomialP := inferInstance
  isPolynomialQ := inferInstance
  toB := toB
  toC := toC

/-- The first factor of `of toB toC` is the source of `toB`. -/
theorem of_P {P Q : Type u} [CommRing P] [CommRing Q]
    [Algebra A P] [Algebra P Q]
    [Algebra.IsPolynomial A P] [Algebra.IsPolynomial P Q]
    (toB : P →ₐ[A] B) (toC : @AlgHom P Q C _ _ _ _ (algebraPCOf toB)) :
    (of A B C toB toC).P = P := sorry

/-- The second factor of `of toB toC` is the source of `toC`. -/
theorem of_Q {P Q : Type u} [CommRing P] [CommRing Q]
    [Algebra A P] [Algebra P Q]
    [Algebra.IsPolynomial A P] [Algebra.IsPolynomial P Q]
    (toB : P →ₐ[A] B) (toC : @AlgHom P Q C _ _ _ _ (algebraPCOf toB)) :
    (of A B C toB toC).Q = Q := sorry

variable (A B C) in
/-- The standard triple `A[σ] ⟶ B`, `A[σ][τ] ⟶ C` attached to generating maps
`σ → B` and `τ → C`. -/
def ofGenerators (σ τ : Type u) (f : σ → B) (g : τ → C) : PolynomialTriple A B C :=
  let toB := MvPolynomial.aeval f
  { P := MvPolynomial σ A
    commRingP := inferInstance
    algebraAP := inferInstance
    Q := MvPolynomial τ (MvPolynomial σ A)
    commRingQ := inferInstance
    algebraPQ := inferInstance
    isPolynomialP := inferInstance
    isPolynomialQ := inferInstance
    toB := toB
    toC :=
      @MvPolynomial.aeval (MvPolynomial σ A) C τ inferInstance inferInstance
        (algebraPCOf toB) g }

/-- The first ring of `ofGenerators σ τ f g` is `A[σ]`. -/
theorem ofGenerators_P (σ τ : Type u) (f : σ → B) (g : τ → C) :
    (ofGenerators A B C σ τ f g).P = MvPolynomial σ A := sorry

/-- The second ring of `ofGenerators σ τ f g` is `A[σ][τ]`. -/
theorem ofGenerators_Q (σ τ : Type u) (f : σ → B) (g : τ → C) :
    (ofGenerators A B C σ τ f g).Q = MvPolynomial τ (MvPolynomial σ A) := sorry

/-- The underlying ring map of the `P`-algebra map `Q ⟶ C`. -/
def toCRingHom (X : PolynomialTriple A B C) : X.Q →+* C :=
  @AlgHom.toRingHom X.P X.Q C _ _ _ X.algebraPQ (algebraPCOf X.toB) X.toC

/-- Unfolding `toCRingHom` recovers the ring homomorphism of `toC`. -/
theorem toCRingHom_eq (X : PolynomialTriple A B C) :
    toCRingHom X = @AlgHom.toRingHom X.P X.Q C _ _ _ X.algebraPQ (algebraPCOf X.toB) X.toC :=
  sorry

/-- The `P`-algebra map `Q ⟶ C` over the composite `P ⟶ B ⟶ C`. -/
def toCAlg (X : PolynomialTriple A B C) :
    @AlgHom X.P X.Q C _ _ _ X.algebraPQ (algebraPCOf X.toB) :=
  X.toC

/-- A morphism of triples is a pair of ring maps, the first an `A`-algebra map over `B` and
the second compatible with the tower `P ⟶ P'` and the maps to `C`. -/
structure Hom (X Y : PolynomialTriple A B C) where
  /-- The map of polynomial `A`-algebras on the first factor. -/
  toP : X.P →ₐ[A] Y.P
  /-- The first-factor map lies over `B`. -/
  commB : Y.toB.comp toP = X.toB
  /-- The underlying ring map of polynomial algebras on the second factor. -/
  toQ : X.Q →+* Y.Q
  /-- The second-factor map is equivariant for `P ⟶ P'`. -/
  commP : toQ.comp (algebraMap X.P X.Q) = (algebraMap Y.P Y.Q).comp toP.toRingHom
  /-- The second-factor map lies over `C`. -/
  commC : (toCRingHom Y).comp toQ = toCRingHom X

/-- The over-`B` and over-`C` conditions of a morphism of triples. -/
theorem Hom.spec {X Y : PolynomialTriple A B C} (f : Hom X Y) :
    Y.toB.comp f.toP = X.toB ∧ (toCRingHom Y).comp f.toQ = toCRingHom X := sorry

/-- The identity first-factor map lies over `B`. -/
theorem Hom.id_commB (X : PolynomialTriple A B C) :
    X.toB.comp (AlgHom.id A X.P) = X.toB := sorry

/-- The identity second-factor map is equivariant for `P`. -/
theorem Hom.id_commP (X : PolynomialTriple A B C) :
    (RingHom.id X.Q).comp (algebraMap X.P X.Q) =
      (algebraMap X.P X.Q).comp (AlgHom.id A X.P).toRingHom := sorry

/-- The identity second-factor map lies over `C`. -/
theorem Hom.id_commC (X : PolynomialTriple A B C) :
    (toCRingHom X).comp (RingHom.id X.Q) = toCRingHom X := sorry

/-- The identity morphism of a triple. -/
def Hom.id (X : PolynomialTriple A B C) : Hom X X where
  toP := AlgHom.id A X.P
  commB := Hom.id_commB X
  toQ := RingHom.id X.Q
  commP := Hom.id_commP X
  commC := Hom.id_commC X

/-- Composite first-factor maps lie over `B`. -/
theorem Hom.comp_commB {X Y Z : PolynomialTriple A B C} (f : Hom X Y) (g : Hom Y Z) :
    Z.toB.comp (g.toP.comp f.toP) = X.toB := sorry

/-- Composite second-factor maps are equivariant for `P`. -/
theorem Hom.comp_commP {X Y Z : PolynomialTriple A B C} (f : Hom X Y) (g : Hom Y Z) :
    (g.toQ.comp f.toQ).comp (algebraMap X.P X.Q) =
      (algebraMap Z.P Z.Q).comp (g.toP.comp f.toP).toRingHom := sorry

/-- Composite second-factor maps lie over `C`. -/
theorem Hom.comp_commC {X Y Z : PolynomialTriple A B C} (f : Hom X Y) (g : Hom Y Z) :
    (toCRingHom Z).comp (g.toQ.comp f.toQ) = toCRingHom X := sorry

/-- Composition of morphisms of triples. -/
def Hom.comp {X Y Z : PolynomialTriple A B C} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  toP := g.toP.comp f.toP
  commB := Hom.comp_commB f g
  toQ := g.toQ.comp f.toQ
  commP := Hom.comp_commP f g
  commC := Hom.comp_commC f g

/-- Left identity law for morphisms of triples. -/
theorem Hom.id_comp {X Y : PolynomialTriple A B C} (f : Hom X Y) :
    Hom.comp (Hom.id X) f = f := sorry

/-- Right identity law for morphisms of triples. -/
theorem Hom.comp_id {X Y : PolynomialTriple A B C} (f : Hom X Y) :
    Hom.comp f (Hom.id Y) = f := sorry

/-- Associativity of composition of morphisms of triples. -/
theorem Hom.assoc {W X Y Z : PolynomialTriple A B C}
    (f : Hom W X) (g : Hom X Y) (h : Hom Y Z) :
    Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h) := sorry

/-- The covariant category of polynomial triples over `A ⟶ B ⟶ C`. -/
instance : Category (PolynomialTriple A B C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

variable (A B C) in
/-- The opposite of the category of triples, i.e. the site `C_{C/B/A}`. -/
abbrev site := (PolynomialTriple A B C)ᵒᵖ

/-- The `P`-algebra structure on `B` induced by `toB`. -/
@[reducible] def algebraPB (X : PolynomialTriple A B C) : Algebra X.P B :=
  RingHom.toAlgebra X.toB.toRingHom

/-- Unfolding `algebraPB` recovers the algebra of `toB`. -/
theorem algebraPB_eq (X : PolynomialTriple A B C) :
    algebraPB X = RingHom.toAlgebra X.toB.toRingHom := sorry

/-- The `A`-algebra structure on `Q` obtained by restriction of scalars along `A ⟶ P`. -/
@[reducible] def algebraAQ (X : PolynomialTriple A B C) : Algebra A X.Q :=
  RingHom.toAlgebra ((algebraMap X.P X.Q).comp (algebraMap A X.P))

/-- Unfolding `algebraAQ` recovers restriction of scalars along `A ⟶ P`. -/
theorem algebraAQ_eq (X : PolynomialTriple A B C) :
    algebraAQ X = RingHom.toAlgebra ((algebraMap X.P X.Q).comp (algebraMap A X.P)) := sorry

/-- The `P`-algebra structure on `C` induced by `P ⟶ B ⟶ C`. -/
@[reducible] def algebraPC (X : PolynomialTriple A B C) : Algebra X.P C :=
  algebraPCOf X.toB

/-- Unfolding `algebraPC` recovers the composite algebra `P ⟶ B ⟶ C`. -/
theorem algebraPC_eq (X : PolynomialTriple A B C) :
    algebraPC X = algebraPCOf X.toB := sorry

/-- Package an algebra map from a polynomial source as an object of `PolynomialOver`. -/
def toPolynomialOver {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {P : Type u} [CommRing P] [Algebra R P] [Algebra.IsPolynomial R P]
    (f : P →ₐ[R] S) : Algebra.PolynomialOver R S where
  obj := Over.mk (CommAlgCat.ofHom f)
  property := ‹Algebra.IsPolynomial R P›

/-- The covariant form of `u1`, sending `(P ⟶ B, Q ⟶ C)` to `(P ⟶ B)`. -/
def forgetToBaseObj (X : PolynomialTriple A B C) : Algebra.PolynomialOver A B :=
  toPolynomialOver X.toB

/-- The over-`B` triangle of a first-factor map. -/
theorem forgetToBaseMap_w {X Y : PolynomialTriple A B C} (f : Hom X Y) :
    CommAlgCat.ofHom f.toP ≫ (forgetToBaseObj Y).obj.hom =
      (forgetToBaseObj X).obj.hom := sorry

/-- The morphism of polynomial `A`-algebras over `B` induced by a morphism of triples. -/
def forgetToBaseMap {X Y : PolynomialTriple A B C} (f : Hom X Y) :
    forgetToBaseObj X ⟶ forgetToBaseObj Y :=
  ObjectProperty.homMk (Over.homMk (CommAlgCat.ofHom f.toP) (forgetToBaseMap_w f))

/-- Identity morphisms project to identity morphisms over `B`. -/
theorem forgetToBase_map_id (X : PolynomialTriple A B C) :
    forgetToBaseMap (Hom.id X) = 𝟙 (forgetToBaseObj X) := sorry

/-- Composition of triples projects to composition over `B`. -/
theorem forgetToBase_map_comp {X Y Z : PolynomialTriple A B C} (f : Hom X Y) (g : Hom Y Z) :
    forgetToBaseMap (Hom.comp f g) = forgetToBaseMap f ≫ forgetToBaseMap g := sorry

variable (A B C) in
/-- The covariant form of `u1`, sending `(P ⟶ B, Q ⟶ C)` to `(P ⟶ B)`. -/
def forgetToBase : PolynomialTriple A B C ⥤ Algebra.PolynomialOver A B where
  obj := forgetToBaseObj
  map f := forgetToBaseMap f
  map_id X := forgetToBase_map_id X
  map_comp f g := forgetToBase_map_comp f g

/-- Objects of `forgetToBase` are the first-factor polynomial algebras over `B`. -/
theorem forgetToBase_obj (X : PolynomialTriple A B C) :
    (forgetToBase A B C).obj X = forgetToBaseObj X := sorry

/-- The `A`-algebra map `Q ⟶ C` in the presence of restriction of scalars along `A ⟶ P`. -/
def toCOverAWith (X : PolynomialTriple A B C) [Algebra A X.Q] : X.Q →ₐ[A] C :=
  { toCRingHom X with commutes' := sorry }

/-- The `A`-algebra map `Q ⟶ C` obtained by viewing `Q` as an `A`-algebra via `A ⟶ P`. -/
def toCOverA (X : PolynomialTriple A B C) :=
  @toCOverAWith A B C _ _ _ _ _ _ _ X (algebraAQ X)

/-- Restriction of scalars of a polynomial `P`-algebra along `A ⟶ P` is a polynomial
`A`-algebra, for the algebra structure `algebraAQ`. -/
theorem isPolynomial_algebraAQ (X : PolynomialTriple A B C) :
    @Algebra.IsPolynomial A X.Q _ _ (algebraAQ X) := sorry

/-- The covariant form of `u2` on objects, in the presence of `Algebra A Q`. -/
def forgetToOverAObjWith (X : PolynomialTriple A B C) [Algebra A X.Q]
    [Algebra.IsPolynomial A X.Q] :
    Algebra.PolynomialOver A C :=
  toPolynomialOver (toCOverAWith X)

/-- The covariant form of `u2` on objects, sending `(P ⟶ B, Q ⟶ C)` to the same ring `Q`
viewed as an `A`-algebra map to `C`. -/
def forgetToOverAObj (X : PolynomialTriple A B C) : Algebra.PolynomialOver A C :=
  @toPolynomialOver A C _ _ _ X.Q _ (algebraAQ X) (isPolynomial_algebraAQ X) (toCOverA X)

/-- A second-factor ring map is an `A`-algebra map. -/
def forgetToOverAMapAlgWith {X Y : PolynomialTriple A B C} (f : Hom X Y)
    [Algebra A X.Q] [Algebra A Y.Q] : X.Q →ₐ[A] Y.Q :=
  { f.toQ with commutes' := sorry }

/-- The over-`C` triangle of a second-factor map, viewed over `A`. -/
theorem forgetToOverAMap_wWith {X Y : PolynomialTriple A B C} (f : Hom X Y)
    [Algebra A X.Q] [Algebra A Y.Q]
    [Algebra.IsPolynomial A X.Q] [Algebra.IsPolynomial A Y.Q] :
    CommAlgCat.ofHom (forgetToOverAMapAlgWith f) ≫ (forgetToOverAObjWith Y).obj.hom =
      (forgetToOverAObjWith X).obj.hom := sorry

/-- The morphism of polynomial `A`-algebras over `C` induced by a morphism of triples,
in the presence of restriction of scalars. -/
def forgetToOverAMapWith {X Y : PolynomialTriple A B C} (f : Hom X Y)
    [Algebra A X.Q] [Algebra A Y.Q]
    [Algebra.IsPolynomial A X.Q] [Algebra.IsPolynomial A Y.Q] :
    forgetToOverAObjWith X ⟶ forgetToOverAObjWith Y :=
  ObjectProperty.homMk
    (Over.homMk (CommAlgCat.ofHom (forgetToOverAMapAlgWith f)) (forgetToOverAMap_wWith f))

/-- The morphism of polynomial `A`-algebras over `C` induced by a morphism of triples. -/
def forgetToOverAMap {X Y : PolynomialTriple A B C} (f : Hom X Y) :
    forgetToOverAObj X ⟶ forgetToOverAObj Y :=
  @forgetToOverAMapWith A B C _ _ _ _ _ _ _ X Y f (algebraAQ X) (algebraAQ Y)
    (isPolynomial_algebraAQ X) (isPolynomial_algebraAQ Y)

/-- Identity morphisms project to identity morphisms over `C` as an `A`-algebra. -/
theorem forgetToOverA_map_id (X : PolynomialTriple A B C) :
    forgetToOverAMap (Hom.id X) = 𝟙 (forgetToOverAObj X) := sorry

/-- Composition of triples projects to composition over `C` as an `A`-algebra. -/
theorem forgetToOverA_map_comp {X Y Z : PolynomialTriple A B C} (f : Hom X Y) (g : Hom Y Z) :
    forgetToOverAMap (Hom.comp f g) = forgetToOverAMap f ≫ forgetToOverAMap g := sorry

variable (A B C) in
/-- The covariant form of `u2`, sending `(P ⟶ B, Q ⟶ C)` to `(Q ⟶ C)` as an `A`-algebra. -/
def forgetToOverA : PolynomialTriple A B C ⥤ Algebra.PolynomialOver A C where
  obj := forgetToOverAObj
  map f := forgetToOverAMap f
  map_id X := forgetToOverA_map_id X
  map_comp f g := forgetToOverA_map_comp f g

/-- Objects of `forgetToOverA` are the second-factor rings `Q` mapping to `C` over `A`. -/
theorem forgetToOverA_obj (X : PolynomialTriple A B C) :
    (forgetToOverA A B C).obj X = forgetToOverAObj X := sorry

/-- Rebuild `toC` as a `P`-algebra map using a given `P`-algebra structure on `C`. -/
def toCAlgWith (X : PolynomialTriple A B C) [Algebra X.P C] : X.Q →ₐ[X.P] C :=
  { toCRingHom X with commutes' := sorry }

/-- The `P`-algebra map `B ⟶ C` associated to a triple, in the presence of `P`-algebras on
`B` and `C`. -/
def toCOverPWith (X : PolynomialTriple A B C) [Algebra X.P B] [Algebra X.P C] :
    B →ₐ[X.P] C :=
  { (algebraMap B C : B →+* C) with commutes' := sorry }

/-- The `P`-algebra map `B ⟶ C` associated to a triple. -/
def toCOverP (X : PolynomialTriple A B C) :=
  @toCOverPWith A B C _ _ _ _ _ _ _ X (algebraPB X) (algebraPCOf X.toB)

/-- The `B`-algebra map `Q ⊗[P] B ⟶ C`, in the presence of the derived tensor algebra. -/
def tensorToCWith (X : PolynomialTriple A B C)
    [Algebra X.P B] [Algebra X.P C] [Algebra B (X.Q ⊗[X.P] B)] :
    (X.Q ⊗[X.P] B) →ₐ[B] C :=
  { (Algebra.TensorProduct.productMap (toCAlgWith X) (toCOverPWith X)).toRingHom with
    commutes' := sorry }

/-- The `B`-algebra map `Q ⊗[P] B ⟶ C`. -/
def tensorToC (X : PolynomialTriple A B C) :=
  @tensorToCWith A B C _ _ _ _ _ _ _ X (algebraPB X) (algebraPCOf X.toB)
    (@Algebra.TensorProduct.rightAlgebra X.P X.Q B _ _ _ _ (algebraPB X))

/-- The ring map of `tensorToC` is the product of `Q ⟶ C` and `B ⟶ C`. -/
theorem tensorToC_toRingHom (X : PolynomialTriple A B C)
    [Algebra X.P B] [Algebra X.P C] [Algebra B (X.Q ⊗[X.P] B)] :
    (tensorToCWith X).toRingHom =
      (Algebra.TensorProduct.productMap (toCAlgWith X) (toCOverPWith X)).toRingHom := sorry

/-- The base-change `Q ⊗[P] B` is a polynomial `B`-algebra for `TensorProduct.rightAlgebra`
induced by `algebraPB`. -/
theorem isPolynomial_tensorOverBase (X : PolynomialTriple A B C) :
    @Algebra.IsPolynomial B
      (@TensorProduct X.P _ X.Q B _ _ _ (algebraPB X).toModule) _ _
      (@Algebra.TensorProduct.rightAlgebra X.P X.Q B _ _ _ _ (algebraPB X)) := sorry

/-- The covariant form of `u3` on objects, in the presence of the derived tensor algebra. -/
def tensorOverBaseWith (X : PolynomialTriple A B C)
    [Algebra X.P B] [Algebra X.P C] [Algebra B (X.Q ⊗[X.P] B)]
    [Algebra.IsPolynomial B (X.Q ⊗[X.P] B)] :
    Algebra.PolynomialOver B C :=
  toPolynomialOver (tensorToCWith X)

/-- The covariant form of `u3` on objects, sending `(P ⟶ B, Q ⟶ C)` to `(Q ⊗[P] B ⟶ C)`. -/
def tensorOverBase (X : PolynomialTriple A B C) : Algebra.PolynomialOver B C :=
  @tensorOverBaseWith A B C _ _ _ _ _ _ _ X (algebraPB X) (algebraPCOf X.toB)
    (@Algebra.TensorProduct.rightAlgebra X.P X.Q B _ _ _ _ (algebraPB X))
    (isPolynomial_tensorOverBase X)

/-- The `P`-algebra structure on a target tensor `Q' ⊗[P'] B` via `P ⟶ B`. -/
@[reducible] def algebraPOnTensorWith (X Y : PolynomialTriple A B C)
    [Algebra Y.P B] [Algebra B (Y.Q ⊗[Y.P] B)] [Algebra X.P B] :
    Algebra X.P (Y.Q ⊗[Y.P] B) :=
  RingHom.toAlgebra ((algebraMap B (Y.Q ⊗[Y.P] B)).comp (algebraMap X.P B))

/-- The left factor of a tensor map of triples, as a `P`-algebra map. -/
def forgetToOverBMapLeftWith {X Y : PolynomialTriple A B C} (f : Hom X Y)
    [Algebra X.P B] [Algebra Y.P B] [Algebra B (Y.Q ⊗[Y.P] B)]
    [Algebra X.P (Y.Q ⊗[Y.P] B)] :
    X.Q →ₐ[X.P] (Y.Q ⊗[Y.P] B) :=
  { ((Algebra.TensorProduct.includeLeftRingHom : Y.Q →+* Y.Q ⊗[Y.P] B).comp f.toQ) with
    commutes' := sorry }

/-- The right factor of a tensor map of triples, as a `P`-algebra map. -/
def forgetToOverBMapRightWith {X Y : PolynomialTriple A B C} (f : Hom X Y)
    [Algebra X.P B] [Algebra Y.P B] [Algebra B (Y.Q ⊗[Y.P] B)]
    [Algebra X.P (Y.Q ⊗[Y.P] B)] :
    B →ₐ[X.P] (Y.Q ⊗[Y.P] B) :=
  { (Algebra.TensorProduct.includeRight : B →ₐ[Y.P] Y.Q ⊗[Y.P] B).toRingHom with
    commutes' := sorry }

/-- The ring map `Q ⊗[P] B ⟶ Q' ⊗[P'] B` induced by a morphism of triples. -/
def forgetToOverBMapRingHomWith {X Y : PolynomialTriple A B C} (f : Hom X Y)
    [Algebra X.P B] [Algebra Y.P B] [Algebra B (Y.Q ⊗[Y.P] B)]
    [Algebra X.P (Y.Q ⊗[Y.P] B)] :
    (X.Q ⊗[X.P] B) →+* (Y.Q ⊗[Y.P] B) :=
  (Algebra.TensorProduct.productMap (forgetToOverBMapLeftWith f)
    (forgetToOverBMapRightWith f)).toRingHom

/-- The `B`-algebra map `Q ⊗[P] B ⟶ Q' ⊗[P'] B` induced by a morphism of triples. -/
def forgetToOverBMapAlgWith {X Y : PolynomialTriple A B C} (f : Hom X Y)
    [Algebra X.P B] [Algebra Y.P B]
    [Algebra B (X.Q ⊗[X.P] B)] [Algebra B (Y.Q ⊗[Y.P] B)]
    [Algebra X.P (Y.Q ⊗[Y.P] B)] :
    (X.Q ⊗[X.P] B) →ₐ[B] (Y.Q ⊗[Y.P] B) :=
  { forgetToOverBMapRingHomWith f with commutes' := sorry }

/-- The `B`-algebra map `Q ⊗[P] B ⟶ Q' ⊗[P'] B` induced by a morphism of triples. -/
def forgetToOverBMapAlg {X Y : PolynomialTriple A B C} (f : Hom X Y) :=
  @forgetToOverBMapAlgWith A B C _ _ _ _ _ _ _ X Y f (algebraPB X) (algebraPB Y)
    (@Algebra.TensorProduct.rightAlgebra X.P X.Q B _ _ _ _ (algebraPB X))
    (@Algebra.TensorProduct.rightAlgebra Y.P Y.Q B _ _ _ _ (algebraPB Y))
    (@algebraPOnTensorWith A B C _ _ _ _ _ _ _ X Y (algebraPB Y)
      (@Algebra.TensorProduct.rightAlgebra Y.P Y.Q B _ _ _ _ (algebraPB Y))
      (algebraPB X))

/-- The over-`C` triangle of a tensor map of triples. -/
theorem forgetToOverBMap_wWith {X Y : PolynomialTriple A B C} (f : Hom X Y)
    [Algebra X.P B] [Algebra X.P C] [Algebra Y.P B] [Algebra Y.P C]
    [Algebra B (X.Q ⊗[X.P] B)] [Algebra B (Y.Q ⊗[Y.P] B)]
    [Algebra X.P (Y.Q ⊗[Y.P] B)]
    [Algebra.IsPolynomial B (X.Q ⊗[X.P] B)]
    [Algebra.IsPolynomial B (Y.Q ⊗[Y.P] B)] :
    CommAlgCat.ofHom (forgetToOverBMapAlgWith f) ≫ (tensorOverBaseWith Y).obj.hom =
      (tensorOverBaseWith X).obj.hom := sorry

/-- The morphism of polynomial `B`-algebras over `C` induced by a morphism of triples,
in the presence of the derived tensor algebras. -/
def forgetToOverBMapWith {X Y : PolynomialTriple A B C} (f : Hom X Y)
    [Algebra X.P B] [Algebra X.P C] [Algebra Y.P B] [Algebra Y.P C]
    [Algebra B (X.Q ⊗[X.P] B)] [Algebra B (Y.Q ⊗[Y.P] B)]
    [Algebra X.P (Y.Q ⊗[Y.P] B)]
    [Algebra.IsPolynomial B (X.Q ⊗[X.P] B)]
    [Algebra.IsPolynomial B (Y.Q ⊗[Y.P] B)] :
    tensorOverBaseWith X ⟶ tensorOverBaseWith Y :=
  ObjectProperty.homMk
    (Over.homMk (CommAlgCat.ofHom (forgetToOverBMapAlgWith f)) (forgetToOverBMap_wWith f))

/-- The morphism of polynomial `B`-algebras over `C` induced by a morphism of triples. -/
def forgetToOverBMap {X Y : PolynomialTriple A B C} (f : Hom X Y) :
    tensorOverBase X ⟶ tensorOverBase Y :=
  @forgetToOverBMapWith A B C _ _ _ _ _ _ _ X Y f (algebraPB X) (algebraPCOf X.toB)
    (algebraPB Y) (algebraPCOf Y.toB)
    (@Algebra.TensorProduct.rightAlgebra X.P X.Q B _ _ _ _ (algebraPB X))
    (@Algebra.TensorProduct.rightAlgebra Y.P Y.Q B _ _ _ _ (algebraPB Y))
    (@algebraPOnTensorWith A B C _ _ _ _ _ _ _ X Y (algebraPB Y)
      (@Algebra.TensorProduct.rightAlgebra Y.P Y.Q B _ _ _ _ (algebraPB Y))
      (algebraPB X))
    (isPolynomial_tensorOverBase X) (isPolynomial_tensorOverBase Y)

/-- Identity morphisms tensor to identity morphisms over `C` as a `B`-algebra. -/
theorem forgetToOverB_map_id (X : PolynomialTriple A B C) :
    forgetToOverBMap (Hom.id X) = 𝟙 (tensorOverBase X) := sorry

/-- Composition of triples tensors to composition over `C` as a `B`-algebra. -/
theorem forgetToOverB_map_comp {X Y Z : PolynomialTriple A B C} (f : Hom X Y) (g : Hom Y Z) :
    forgetToOverBMap (Hom.comp f g) = forgetToOverBMap f ≫ forgetToOverBMap g := sorry

variable (A B C) in
/-- The covariant form of `u3`, sending `(P ⟶ B, Q ⟶ C)` to `(Q ⊗[P] B ⟶ C)`. -/
def forgetToOverB : PolynomialTriple A B C ⥤ Algebra.PolynomialOver B C where
  obj := tensorOverBase
  map f := forgetToOverBMap f
  map_id X := forgetToOverB_map_id X
  map_comp f g := forgetToOverB_map_comp f g

/-- Objects of `forgetToOverB` are the tensors `Q ⊗[P] B` mapping to `C`. -/
theorem forgetToOverB_obj (X : PolynomialTriple A B C) :
    (forgetToOverB A B C).obj X = tensorOverBase X := sorry

/-- The source of `forgetToBaseObj X` is the ring `P`. -/
theorem forgetToBaseObj_left (X : PolynomialTriple A B C) :
    (forgetToBaseObj X).obj.left = CommAlgCat.of A X.P := sorry

/-- The source of `forgetToOverAObj X` is the ring `Q`. -/
theorem forgetToOverAObj_left (X : PolynomialTriple A B C) [Algebra A X.Q]
    [Algebra.IsPolynomial A X.Q] :
    (forgetToOverAObjWith X).obj.left = CommAlgCat.of A X.Q := sorry

/-- The source of `tensorOverBase X` is the ring `Q ⊗[P] B`. -/
theorem tensorOverBase_left (X : PolynomialTriple A B C)
    [Algebra X.P B] [Algebra X.P C] [Algebra B (X.Q ⊗[X.P] B)]
    [Algebra.IsPolynomial B (X.Q ⊗[X.P] B)] :
    (tensorOverBaseWith X).obj.left = CommAlgCat.of B (X.Q ⊗[X.P] B) := sorry

end PolynomialTriple

end RingedSite.Cotangent
