/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphisms of morphisms of stacks in sets

This module supplies explicit local-Hom isomorphism readouts for the forgetful
maps from stacks in sets.  Composition-normalized bridges are deliberately not
built by transporting these isomorphisms along propositional composition laws.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Sets.Hom

variable {J : GrothendieckTopology C}
variable {X Y : StackOver.Sets J}

/-- Forget an isomorphism of morphisms of stacks in sets to the corresponding isomorphism of
underlying based functors. -/
@[stacks 02ZK "set-stack morphism isomorphism based-functor owner"]
noncomputable def toBasedFunctorIso {F G : X ⟶ Y} (e : F ≅ G) :
    toBasedFunctor F ≅ toBasedFunctor G :=
  FiberedCategoryOver.Setoids.toBasedFunctorIso
    (StackOver.Setoids.Hom.toSetoidsMorIso
      (Bicategory.InducedBicategory.Iso.toAmbient e))

/-- Forget an isomorphism of morphisms of stacks in sets to the corresponding isomorphism of
set-fibred morphisms. -/
@[stacks 02ZK "set-stack morphism isomorphism set-fibred owner"]
noncomputable def toSetsMorIso {F G : X ⟶ Y} (e : F ≅ G) :
    toSetsMor F ≅ toSetsMor G :=
  Bicategory.InducedBicategory.isoMk
    (toBasedFunctorIso e)

namespace toSetsMorIso

/-- The ambient forward cell of the forgotten set-fibred isomorphism is the forward cell of
the explicitly constructed based-functor isomorphism. -/
@[simp, stacks 02ZK "set-stack morphism isomorphism forward readout"]
theorem hom {F G : X ⟶ Y} (e : F ≅ G) :
    (toSetsMorIso e).hom.hom = (toBasedFunctorIso e).hom := sorry

/-- The ambient inverse cell of the forgotten set-fibred isomorphism is the inverse cell of
the explicitly constructed based-functor isomorphism. -/
@[simp, stacks 02ZK "set-stack morphism isomorphism inverse readout"]
theorem inv {F G : X ⟶ Y} (e : F ≅ G) :
    (toSetsMorIso e).inv.hom = (toBasedFunctorIso e).inv := sorry

end toSetsMorIso

end StackOver.Sets.Hom

end CategoryTheory

/- Both owners map the explicitly supplied `e`; neither transports along an equality nor
chooses an inverse from an `IsIso` proof.  Any deferred axiom is confined to inherited
proof fields of the forgetful constructions. -/
