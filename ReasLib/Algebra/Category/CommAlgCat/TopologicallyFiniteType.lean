/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.RingTheory.AdicCompletion.TopologicallyFiniteType

/-!
# The category of topologically finite type algebras

Topologically finite type algebras form a full subcategory of commutative algebras,
with all algebra maps as morphisms.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CommAlgCat

variable (R : Type u) [CommRing R] (I : Ideal R)

/-- The object property of `I`-adically complete `R`-algebras whose special fiber is of
finite type over `R ⧸ I`. -/
abbrev topologicallyFiniteType : ObjectProperty (CommAlgCat.{v} R) :=
  fun S ↦ Algebra.TopologicallyFiniteType I S

/-- The full subcategory of `I`-adically complete `R`-algebras whose special fiber is of
finite type over `R ⧸ I`. Morphisms are `R`-algebra maps. -/
abbrev TopologicallyFiniteType (R : Type u) [CommRing R] (I : Ideal R) : Type _ :=
  (topologicallyFiniteType.{v} R I).FullSubcategory

namespace TopologicallyFiniteType

/-- An object of `CommAlgCat.TopologicallyFiniteType` coerces to its underlying carrier. -/
instance instCoeSort : CoeSort (TopologicallyFiniteType.{v} R I) (Type v) :=
  ⟨fun S ↦ S.obj⟩

/-- An object of `CommAlgCat.TopologicallyFiniteType` is topologically of finite type. -/
instance instAlgebraTopologicallyFiniteType (S : TopologicallyFiniteType.{v} R I) :
    Algebra.TopologicallyFiniteType I S :=
  S.property

/-- Bundle an `R`-algebra that is topologically of finite type with respect to `I`. -/
@[simps obj]
abbrev of (S : Type v) [CommRing S] [Algebra R S] [Algebra.TopologicallyFiniteType I S] :
    TopologicallyFiniteType.{v} R I where
  obj := .of R S
  property := ‹_›

/-- The inclusion of topologically finite type algebras into commutative `R`-algebras. -/
abbrev inclusion : TopologicallyFiniteType.{v} R I ⥤ CommAlgCat.{v} R :=
  (topologicallyFiniteType.{v} R I).ι

variable {R I}

/-- Construct a morphism in `CommAlgCat.TopologicallyFiniteType` from an algebra map. -/
@[simps]
abbrev ofHom {S T : Type v} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra.TopologicallyFiniteType I S] [Algebra.TopologicallyFiniteType I T]
    (f : S →ₐ[R] T) :
    of R I S ⟶ of R I T where
  hom := CommAlgCat.ofHom f

/-- Construct an isomorphism in `CommAlgCat.TopologicallyFiniteType` from an algebra
equivalence. -/
abbrev isoMk {S T : TopologicallyFiniteType.{v} R I} (e : S.obj ≃ₐ[R] T.obj) :
    S ≅ T :=
  ObjectProperty.isoMk _ (CommAlgCat.isoMk e)

end TopologicallyFiniteType

end CommAlgCat
