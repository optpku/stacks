/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry

universe u

open CategoryTheory

/-
Definition 29.8.1: A morphism of schemes `f : X ⟶ S` is dominant if its image is dense in `S`.
-/
@[stacks 01RJ] #check
  (AlgebraicGeometry.IsDominant : ∀ {X S : Scheme.{u}}, (X ⟶ S) → Prop)

#check
  (AlgebraicGeometry.isDominant_iff : ∀ {X S : Scheme.{u}} (f : X ⟶ S),
    AlgebraicGeometry.IsDominant f ↔ DenseRange f)

end AlgebraicGeometry
