/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Flattening
import StacksCheckRecall

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent]

/- 38.20.13.1: the contravariant flattening functor on schemes over `S` is singleton exactly
when the pullback of the quasicoherent module is flat over the new base, and empty otherwise. -/
@[stacks 05MX] #check
  (AlgebraicGeometry.Scheme.Modules.Flattening.functor f ℱ : (Over S)ᵒᵖ ⥤ Type u)

#check (AlgebraicGeometry.Scheme.Modules.Flattening.functor_obj_nonempty_iff f ℱ :
  ∀ T : Over S,
    Nonempty ((AlgebraicGeometry.Scheme.Modules.Flattening.functor f ℱ).obj (op T)) ↔
      AlgebraicGeometry.Scheme.Modules.Flattening.isFlat f ℱ T)

#check (AlgebraicGeometry.Scheme.Modules.Flattening.functor_obj_unique f ℱ :
  ∀ (T : Over S)
    (x y : (AlgebraicGeometry.Scheme.Modules.Flattening.functor f ℱ).obj (op T)), x = y)

end AlgebraicGeometry
