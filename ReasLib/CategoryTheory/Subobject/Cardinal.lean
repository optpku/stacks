/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.HasCardinalLT
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cardinality of Subobject Lattices

This file compares subobject lattices along monomorphisms and epimorphisms. The monomorphism
comparison is category-theoretic; the epimorphism comparison uses stability of epimorphisms under
pullback in an abelian category.
-/

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.Subobject

variable {C : Type u} [Category.{v} C]

/-- The cardinal of the subobject lattice, represented in a universe in which that lattice is
small. This is the reusable formalization of the size notation `|X|` for an object. -/
@[stacks 079J "small-universe subobject cardinal"]
noncomputable abbrev smallCardinal (X : C) [Small.{w} (Subobject X)] : Cardinal.{w} :=
  Cardinal.mk (Shrink.{w} (Subobject X))

/-- The subobject lattice of the source of a monomorphism has cardinality at most that of its
target. -/
@[stacks 079D "monomorphism"]
theorem cardinalMk_le_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] :
    Cardinal.mk (Subobject X) ≤ Cardinal.mk (Subobject Y) := sorry

/-- Isomorphic objects have equally large subobject lattices. -/
theorem cardinalMk_eq_of_iso {X Y : C} (e : X ≅ Y) :
    Cardinal.mk (Subobject X) = Cardinal.mk (Subobject Y) := sorry

section Abelian

variable [Abelian C]

/-- Pushing a pulled-back subobject forward along an epimorphism recovers the original
subobject. -/
theorem exists_obj_pullback_obj_eq_of_epi {X Y : C} (f : X ⟶ Y) [Epi f]
    (P : Subobject Y) :
    (Subobject.exists f).obj ((Subobject.pullback f).obj P) = P := sorry

/-- Pullback along an epimorphism embeds the subobject lattice of the target into that of the
source. -/
theorem pullback_obj_injective_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] :
    Function.Injective (Subobject.pullback f).obj := sorry

/-- The subobject lattice of the target of an epimorphism has cardinality at most that of its
source. -/
@[stacks 079D "epimorphism"]
theorem cardinalMk_le_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] :
    Cardinal.mk (Subobject Y) ≤ Cardinal.mk (Subobject X) := sorry

/-- The image of a morphism has no more subobjects than its source. -/
theorem cardinalMk_image_le {X Y : C} (f : X ⟶ Y) :
    Cardinal.mk (Subobject (imageSubobject f)) ≤ Cardinal.mk (Subobject X) := sorry

/-- The kernel of a morphism has no more subobjects than its source. -/
theorem cardinalMk_kernel_le {X Y : C} (f : X ⟶ Y) :
    Cardinal.mk (Subobject (kernelSubobject f)) ≤ Cardinal.mk (Subobject X) := sorry

end Abelian

end CategoryTheory.Subobject
