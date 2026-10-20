module

public import ReasLib.CategoryTheory.Abelian.Extension.Isomorphism
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Data.PNat.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Yoneda Extensions with Fixed Endpoints

This module owns finite positive-degree Yoneda extensions in a category with zero morphisms.
They are represented canonically as a full subcategory of `ComposableArrows`: exact rows with
fixed endpoints and monic/epic outer maps. The endpoint-fixed ladder relation is kept separate
from the canonical category structure, so it can be used both for quotient presentations and for
comparisons with degree-one fixed-endpoint extensions.
-/

namespace CategoryTheory

universe v u

open Limits ComposableArrows

section

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A composable row is a degree-`n` Yoneda extension of `B` by `A` when it has the specified
endpoints, is exact at its intermediate objects, and has monic and epic outer maps. -/
structure IsYonedaExtension (A B : C) (n : ℕ+) (E : ComposableArrows C (n + 1)) : Prop where
  /-- The left endpoint of the chain is the fixed object `A`. -/
  left_eq : E.left = A
  /-- The right endpoint of the chain is the fixed object `B`. -/
  right_eq : E.right = B
  /-- The first map `A ⟶ Z_(n-1)` is a monomorphism. -/
  mono_first : Mono (eqToHom left_eq.symm ≫ E.map' 0 1)
  /-- The chain is exact at every intermediate object. -/
  exact : E.Exact
  /-- The last map `Z_0 ⟶ B` is an epimorphism. -/
  epi_last : Epi (E.map' n (n + 1) ≫ eqToHom right_eq)

/-- Definition 13.27.4: a degree `n` Yoneda extension of `B` by `A` is the full subcategory of
exact composable chains `A ⟶ Z_(n-1) ⟶ ... ⟶ Z_0 ⟶ B` with monic first map and epic last map.
Equivalently, these are the chains underlying exact sequences
`0 ⟶ A ⟶ Z_(n-1) ⟶ ... ⟶ Z_0 ⟶ B ⟶ 0`. -/
@[stacks 06XT]
abbrev YonedaExtension (A B : C) (n : ℕ+) :=
  ObjectProperty.FullSubcategory (IsYonedaExtension A B n)

namespace YonedaExtension

variable {A B : C} {n : ℕ+}

/-- The chosen identification of the left endpoint with `A`. -/
abbrev leftEq (E : YonedaExtension A B n) : E.obj.left = A :=
  E.property.left_eq

/-- The chosen identification of the right endpoint with `B`. -/
abbrev rightEq (E : YonedaExtension A B n) : E.obj.right = B :=
  E.property.right_eq

/-- Exactness of the underlying composable chain. -/
abbrev exact (E : YonedaExtension A B n) : E.obj.Exact :=
  E.property.exact

/-- The first nonzero map `A ⟶ Z_(n-1)` in a Yoneda extension. -/
abbrev firstMap (E : YonedaExtension A B n) :
    A ⟶ E.obj.obj' 1 :=
  eqToHom E.leftEq.symm ≫ E.obj.map' 0 1

/-- The last nonzero map `Z_0 ⟶ B` in a Yoneda extension. -/
abbrev lastMap (E : YonedaExtension A B n) :
    E.obj.obj' n ⟶ B :=
  E.obj.map' n (n + 1) ≫ eqToHom E.rightEq

/-- A Yoneda extension carries the canonical monomorphism instance on its first map. -/
instance (E : YonedaExtension A B n) : Mono E.firstMap :=
  E.property.mono_first

/-- A Yoneda extension carries the canonical epimorphism instance on its last map. -/
instance (E : YonedaExtension A B n) : Epi E.lastMap :=
  E.property.epi_last

/-- The two maps in a degree-one Yoneda extension compose to zero. -/
theorem firstMap_comp_lastMap (E : YonedaExtension A B 1) :
    E.firstMap ≫ E.lastMap = 0 := sorry

/-- The degree-one row underlying a Yoneda extension is a short exact sequence. -/
theorem shortExact (E : YonedaExtension A B 1) :
    (ShortComplex.mk E.firstMap E.lastMap E.firstMap_comp_lastMap).ShortExact := sorry

/-- The degree-one fixed-endpoint extension represented by a Yoneda extension. -/
abbrev toExtension (E : YonedaExtension A B 1) : Extension A B where
  E := E.obj.obj' 1
  f := E.firstMap
  g := E.lastMap
  zero := E.firstMap_comp_lastMap
  shortExact := E.shortExact

/-- A ladder between fixed-endpoint Yoneda extensions fixes both endpoints after transport along
their chosen endpoint identifications. -/
def idOnEndpoints (E F : YonedaExtension A B n) (phi : E ⟶ F) : Prop :=
  app' phi.hom 0 = eqToHom (E.leftEq.trans F.leftEq.symm) ∧
    app' phi.hom (n + 1) = eqToHom (E.rightEq.trans F.rightEq.symm)

/-- Two Yoneda extensions of the same degree are equivalent when a third one maps to both by
endpoint-fixed commutative ladders. -/
def Equivalent (E F : YonedaExtension A B n) : Prop :=
  ∃ (G : YonedaExtension A B n) (phi : G ⟶ E) (psi : G ⟶ F),
    idOnEndpoints G E phi ∧ idOnEndpoints G F psi

/-- In degree `1`, categorically isomorphic fixed-endpoint short exact sequences induce
equivalent Yoneda extensions. -/
theorem equivalent_of_toExtension_isIsomorphic {E F : YonedaExtension A B 1}
    (h : IsIsomorphic E.toExtension F.toExtension) :
    Equivalent E F := sorry

end YonedaExtension

end

end CategoryTheory
