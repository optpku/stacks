/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra
public import ReasLib.RingTheory.Henselian.Pair.Basic
public import ReasLib.RingTheory.Henselian.Pair.Category

/-!
# Henselization functor on ring deformation categories

A pair henselization `(P, J) ↦ (P^h, J^h)` induces a functor
`deformationCategory Λ k P ⥤ deformationCategory Λ k P^h` by sending a
deformation `(A, Q) ⟶ (k, P)` to `(A, Q^h) ⟶ (k, P^h)`.
-/

@[expose] public section

open CategoryTheory Functor RingPairCat

universe u

noncomputable section

namespace FlatAlgebraCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (P : Type u) [CommRing P] [Algebra k P]
variable (J : Ideal P)

/-- The henselization ring `P^h` of `(P, J)` as a `k`-algebra, via `k → P → P^h`. -/
instance instAlgebra_henselizationRing :
    Algebra k (henselizationRing (pairOfIdeal J) : Type u) :=
  (RingHom.comp (toHenselization (pairOfIdeal J)) (algebraMap k P)).toAlgebra

/-- Inverse image `J_Q ⊂ Q` of `J` along a deformation `(A, Q) ⟶ (k, P)`. -/
def comapIdeal (x : deformationCategory Λ k P) : Ideal x.left.algebra :=
  Ideal.comap x.hom.toRingHom J

/-- Membership in the inverse-image ideal is membership of the image in `J`. -/
theorem mem_comapIdeal {x : deformationCategory Λ k P} {q : x.left.algebra} :
    q ∈ comapIdeal Λ k P J x ↔ x.hom.toRingHom q ∈ J :=
  Iff.rfl

/-- The inverse-image ideal is the comap of `J` along the deformation ring map. -/
theorem comapIdeal_eq (x : deformationCategory Λ k P) :
    comapIdeal Λ k P J x = Ideal.comap x.hom.toRingHom J :=
  rfl

/-- Pair morphism `(Q, J_Q) ⟶ (P, J)` induced by a deformation `(A, Q) ⟶ (k, P)`. -/
def objPairHom (x : deformationCategory Λ k P) :
    pairOfIdeal (comapIdeal Λ k P J x) ⟶ pairOfIdeal J :=
  InducedCategory.homMk <|
    Arrow.homMk' (CommRingCat.ofHom x.hom.toRingHom)
      (CommRingCat.ofHom
        (Ideal.quotientMap J x.hom.toRingHom
          (le_rfl : comapIdeal Λ k P J x ≤ Ideal.comap x.hom.toRingHom J)))
      (pairOfIdeal_hom_square_of_ringHom (comapIdeal Λ k P J x) J x.hom.toRingHom le_rfl)

/-- The underlying ring homomorphism of `objPairHom` is the deformation ring map. -/
theorem objPairHom_ringHom (x : deformationCategory Λ k P) :
    ringHom (objPairHom Λ k P J x) = x.hom.toRingHom :=
  rfl

/-- The henselization ring `Q^h` of the inverse-image pair `(Q, J_Q)`. -/
abbrev objHenselizationRing (x : deformationCategory Λ k P) : Type u :=
  henselizationRing (pairOfIdeal (comapIdeal Λ k P J x))

/-- `objHenselizationRing` is the chosen henselization ring of `(Q, J_Q)`. -/
theorem objHenselizationRing_eq (x : deformationCategory Λ k P) :
    objHenselizationRing Λ k P J x =
      (henselizationRing (pairOfIdeal (comapIdeal Λ k P J x)) : Type u) :=
  rfl

/-- The henselization `Q^h` is an `A`-algebra via `A → Q → Q^h`. -/
instance instAlgebra_objHenselizationRing (x : deformationCategory Λ k P) :
    Algebra x.left.base.carrier (objHenselizationRing Λ k P J x) :=
  (RingHom.comp (toHenselization (pairOfIdeal (comapIdeal Λ k P J x)))
      (algebraMap x.left.base.carrier x.left.algebra)).toAlgebra

/-- `Q^h` is flat over `A`, as a composite of the flats `A → Q` and `Q → Q^h`. -/
instance instModuleFlat_objHenselizationRing (x : deformationCategory Λ k P) :
    Module.Flat x.left.base.carrier (objHenselizationRing Λ k P J x) :=
  sorry

/-- The object `(A, Q^h)` of `F` attached to a deformation of `P`. -/
def objHenselization (x : deformationCategory Λ k P) : FlatAlgebraCat Λ k :=
  of x.left.base (objHenselizationRing Λ k P J x)

/-- The base of `(A, Q^h)` is the original Artinian local algebra `A`. -/
theorem objHenselization_base (x : deformationCategory Λ k P) :
    (objHenselization Λ k P J x).base = x.left.base :=
  rfl

/-- The algebra of `(A, Q^h)` is the henselization ring of `(Q, J_Q)`. -/
theorem objHenselization_algebra (x : deformationCategory Λ k P) :
    (objHenselization Λ k P J x).algebra = objHenselizationRing Λ k P J x :=
  rfl

/-- The induced henselization map commutes with the base algebra maps. -/
private theorem objHenselizationMap_commutes (x : deformationCategory Λ k P) :
    (henselizationRingMap (objPairHom Λ k P J x)).comp
        (algebraMap (objHenselization Λ k P J x).base.carrier
          (objHenselization Λ k P J x).algebra) =
      (algebraMap
          (ofResidue Λ k (henselizationRing (pairOfIdeal J) : Type u)).base.carrier
          (ofResidue Λ k (henselizationRing (pairOfIdeal J) : Type u)).algebra).comp
        (x.hom.baseHom).hom.toRingHom := sorry

/-- The canonical tensor lift of the induced henselization map is bijective. -/
private theorem objHenselizationMap_isIsoTensor (x : deformationCategory Λ k P) :
    Function.Bijective (canonicalTensorMap
      (Q := objHenselization Λ k P J x) (P := ofResidue Λ k (henselizationRing (pairOfIdeal J) : Type u))
      (x.hom.baseHom) (henselizationRingMap (objPairHom Λ k P J x)) (objHenselizationMap_commutes Λ k P J x)) := sorry

/-- The morphism `(A, Q^h) ⟶ (k, P^h)` attached to a deformation of `P`. -/
def objHenselizationHom (x : deformationCategory Λ k P) :
    objHenselization Λ k P J x ⟶ ofResidue Λ k (henselizationRing (pairOfIdeal J) : Type u) :=
  Hom.of (x.hom.baseHom) (henselizationRingMap (objPairHom Λ k P J x))
    (by exact objHenselizationMap_commutes Λ k P J x) (by exact objHenselizationMap_isIsoTensor Λ k P J x)

/-- The underlying ring map of `objHenselizationHom` is the induced map `Q^h → P^h`. -/
theorem objHenselizationHom_toRingHom (x : deformationCategory Λ k P) :
    (objHenselizationHom Λ k P J x).toRingHom =
      henselizationRingMap (objPairHom Λ k P J x) :=
  rfl

/-- `Q^h → P^h` is linear over `A → k`. -/
theorem objHenselizationHom_commutes (x : deformationCategory Λ k P) :
    (objHenselizationHom Λ k P J x).toRingHom.comp
        (algebraMap (objHenselization Λ k P J x).base.carrier
          (objHenselization Λ k P J x).algebra) =
      (algebraMap
          (ofResidue Λ k (henselizationRing (pairOfIdeal J) : Type u)).base.carrier
          (ofResidue Λ k (henselizationRing (pairOfIdeal J) : Type u)).algebra).comp
        (objHenselizationHom Λ k P J x).baseHom.hom.toRingHom :=
  Hom.commutes (objHenselizationHom Λ k P J x)

/-- The canonical map `k ⊗[A] Q^h → P^h` is bijective. -/
theorem objHenselizationHom_isIso_tensor (x : deformationCategory Λ k P) :
    Function.Bijective
      (canonicalTensorMap (objHenselizationHom Λ k P J x).baseHom
        (objHenselizationHom Λ k P J x).toRingHom
        (objHenselizationHom Λ k P J x).commutes) :=
  Hom.isIso_tensor (objHenselizationHom Λ k P J x)

/-- A morphism of deformations carries inverse-image ideals into inverse-image ideals. -/
theorem mapPairHom_ideal_le {x y : deformationCategory Λ k P} (f : x ⟶ y) :
    comapIdeal Λ k P J x ≤ Ideal.comap f.left.toRingHom (comapIdeal Λ k P J y) :=
  sorry

/-- Pair morphism `(Q, J_Q) ⟶ (Q', J_{Q'})` induced by a morphism of deformations. -/
def mapPairHom {x y : deformationCategory Λ k P} (f : x ⟶ y) :
    pairOfIdeal (comapIdeal Λ k P J x) ⟶ pairOfIdeal (comapIdeal Λ k P J y) :=
  InducedCategory.homMk <|
    Arrow.homMk' (CommRingCat.ofHom f.left.toRingHom)
      (CommRingCat.ofHom
        (Ideal.quotientMap (comapIdeal Λ k P J y) f.left.toRingHom
          (mapPairHom_ideal_le Λ k P J f)))
      (pairOfIdeal_hom_square_of_ringHom (comapIdeal Λ k P J x) (comapIdeal Λ k P J y)
        f.left.toRingHom (mapPairHom_ideal_le Λ k P J f))

/-- The underlying ring homomorphism of `mapPairHom` is the deformation morphism. -/
theorem mapPairHom_ringHom {x y : deformationCategory Λ k P} (f : x ⟶ y) :
    ringHom (mapPairHom Λ k P J f) = f.left.toRingHom :=
  rfl

/-- The induced henselization map commutes with the base algebra maps. -/
private theorem mapHenselizationMap_commutes {x y : deformationCategory Λ k P} (f : x ⟶ y) :
    (henselizationRingMap (mapPairHom Λ k P J f)).comp
        (algebraMap (objHenselization Λ k P J x).base.carrier
          (objHenselization Λ k P J x).algebra) =
      (algebraMap (objHenselization Λ k P J y).base.carrier
          (objHenselization Λ k P J y).algebra).comp
        (f.left.baseHom).hom.toRingHom := sorry

/-- The canonical tensor lift of the induced henselization map is bijective. -/
private theorem mapHenselizationMap_isIsoTensor {x y : deformationCategory Λ k P} (f : x ⟶ y) :
    Function.Bijective (canonicalTensorMap
      (Q := objHenselization Λ k P J x) (P := objHenselization Λ k P J y)
      (f.left.baseHom) (henselizationRingMap (mapPairHom Λ k P J f)) (mapHenselizationMap_commutes Λ k P J f)) := sorry

/-- The morphism `(A, Q^h) ⟶ (A', Q'^h)` induced by a morphism of deformations of `P`. -/
def mapHenselizationHom {x y : deformationCategory Λ k P} (f : x ⟶ y) :
    objHenselization Λ k P J x ⟶ objHenselization Λ k P J y :=
  Hom.of (f.left.baseHom) (henselizationRingMap (mapPairHom Λ k P J f))
    (by exact mapHenselizationMap_commutes Λ k P J f) (by exact mapHenselizationMap_isIsoTensor Λ k P J f)

/-- The underlying ring map of `mapHenselizationHom` is the induced map `Q^h → Q'^h`. -/
theorem mapHenselizationHom_toRingHom {x y : deformationCategory Λ k P} (f : x ⟶ y) :
    (mapHenselizationHom Λ k P J f).toRingHom =
      henselizationRingMap (mapPairHom Λ k P J f) :=
  rfl

/-- `Q^h → Q'^h` is linear over the base map `A → A'`. -/
theorem mapHenselizationHom_commutes {x y : deformationCategory Λ k P} (f : x ⟶ y) :
    (mapHenselizationHom Λ k P J f).toRingHom.comp
        (algebraMap (objHenselization Λ k P J x).base.carrier
          (objHenselization Λ k P J x).algebra) =
      (algebraMap (objHenselization Λ k P J y).base.carrier
          (objHenselization Λ k P J y).algebra).comp
        (mapHenselizationHom Λ k P J f).baseHom.hom.toRingHom :=
  Hom.commutes (mapHenselizationHom Λ k P J f)

/-- The canonical map `A' ⊗[A] Q^h → Q'^h` is bijective. -/
theorem mapHenselizationHom_isIso_tensor {x y : deformationCategory Λ k P} (f : x ⟶ y) :
    Function.Bijective
      (canonicalTensorMap (mapHenselizationHom Λ k P J f).baseHom
        (mapHenselizationHom Λ k P J f).toRingHom
        (mapHenselizationHom Λ k P J f).commutes) :=
  Hom.isIso_tensor (mapHenselizationHom Λ k P J f)

/-- Henselized morphisms commute with the structure maps to `(k, P^h)`. -/
theorem mapHenselizationHom_w {x y : deformationCategory Λ k P} (f : x ⟶ y) :
    mapHenselizationHom Λ k P J f ≫ objHenselizationHom Λ k P J y =
      objHenselizationHom Λ k P J x :=
  sorry

/-- Henselization preserves identity morphisms of deformations. -/
private theorem mapHenselizationHom_id (x : deformationCategory Λ k P) :
    mapHenselizationHom Λ k P J (𝟙 x) = 𝟙 (objHenselization Λ k P J x) := sorry

/-- Henselization preserves composites of deformation morphisms. -/
private theorem mapHenselizationHom_comp {x y z : deformationCategory Λ k P}
    (f : x ⟶ y) (g : y ⟶ z) :
    mapHenselizationHom Λ k P J (f ≫ g) =
      mapHenselizationHom Λ k P J f ≫ mapHenselizationHom Λ k P J g := sorry

/-- The natural functor `Def_P ⥤ Def_{P^h}` induced by pair henselization of `(P, J)`. -/
def henselizationFunctor :
    deformationCategory Λ k P ⥤
      deformationCategory Λ k (henselizationRing (pairOfIdeal J) : Type u) where
  obj x := Over.mk (objHenselizationHom Λ k P J x)
  map f := Over.homMk (mapHenselizationHom Λ k P J f) (mapHenselizationHom_w Λ k P J f)
  map_id x := by
    apply Over.OverMorphism.ext
    exact mapHenselizationHom_id Λ k P J x
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact mapHenselizationHom_comp Λ k P J f g

/-- Objects of `henselizationFunctor` are the henselized deformations `(A, Q^h) ⟶ (k, P^h)`. -/
theorem henselizationFunctor_obj (x : deformationCategory Λ k P) :
    (henselizationFunctor Λ k P J).obj x = Over.mk (objHenselizationHom Λ k P J x) :=
  rfl

/-- Morphisms of `henselizationFunctor` are the henselized deformation morphisms. -/
theorem henselizationFunctor_map {x y : deformationCategory Λ k P} (f : x ⟶ y) :
    (henselizationFunctor Λ k P J).map f =
      Over.homMk (mapHenselizationHom Λ k P J f) (mapHenselizationHom_w Λ k P J f) :=
  rfl

/-- The functor preserves the Artinian local base of a deformation. -/
theorem henselizationFunctor_obj_base (x : deformationCategory Λ k P) :
    ((henselizationFunctor Λ k P J).obj x).left.base = x.left.base :=
  rfl

/-- The functor replaces the algebra of a deformation by its pair henselization. -/
theorem henselizationFunctor_obj_algebra (x : deformationCategory Λ k P) :
    ((henselizationFunctor Λ k P J).obj x).left.algebra =
      objHenselizationRing Λ k P J x :=
  rfl

end FlatAlgebraCat

end
