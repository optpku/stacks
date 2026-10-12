/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
public import stacks_project.Chap37.Lemma_37_61_1
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u

/- Definition 37.61.2: a morphism `f : X ⟶ S` is perfect when it is locally induced by
perfect ring maps; equivalently, `X` is perfect over `S`. -/
@[stacks 0687] #check
  (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsPerfectRingMap :
    {X S : Scheme.{u}} → (X ⟶ S) → Prop)
