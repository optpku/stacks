/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Slice morphisms into monomorphisms

A morphism in a slice category whose target structure arrow is a monomorphism is unique when it
exists.  This leaf exposes that elementary fact directly on `Over`, so downstream APIs need not
repackage their arrows as `MonoOver` merely to obtain comparison uniqueness.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C] {S : C}

/-- Morphisms in a slice category into an object represented by a monomorphism form a
subsingleton. -/
@[stacks 03DP "uniqueness of morphisms over a monomorphism"]
instance homSubsingletonOfMono {X Y : Over S} [Mono Y.hom] :
    Subsingleton (X ⟶ Y) := sorry

/-- Isomorphisms in a slice category into an object represented by a monomorphism form a
subsingleton. -/
@[stacks 03DP "uniqueness of isomorphisms over a monomorphism"]
instance isoSubsingletonOfMono {X Y : Over S} [Mono Y.hom] :
    Subsingleton (X ≅ Y) := sorry

/-- Postcomposition with a monomorphism is full on slice categories. -/
instance map_full_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] :
    (Over.map f).Full := sorry

/-- Postcomposition with a monomorphism is faithful on slice categories. -/
instance map_faithful_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] :
    (Over.map f).Faithful := sorry

end CategoryTheory.Over
