/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Biproduct
public import ReasLib.CategoryTheory.Filtration.Strict
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Strict Biproduct Lifts

Adjoining an arbitrary second component to a strict monomorphism preserves strictness.  The
underlying monomorphism of the biproduct lift is exposed as an instance so downstream proofs do
not need local instance reconstruction.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.FilteredObject.Hom

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasImages C] [HasPullbacks C]
  [HasBinaryBiproducts C]
variable {A B D : FilteredObject C}

/-- A biproduct lift is monic on underlying objects when its first component is monic. -/
instance mono_biprodLift_hom_of_mono_left (f : A ⟶ B) (g : A ⟶ D) [Mono f.hom] :
    Mono (biprod.lift f g).hom := sorry

/-- If `f : A ⟶ B` is a strict monomorphism and `g : A ⟶ D` is arbitrary, then the induced
morphism `A ⟶ B ⊞ D` is strict. -/
@[stacks 05SK]
theorem strict_biprodLift (f : A ⟶ B) (g : A ⟶ D) [Mono f.hom] (hf : Strict f) :
    Strict (biprod.lift f g) := sorry

end CategoryTheory.FilteredObject.Hom
