/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward

/-!
# Affine base change for quasi-coherent modules
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {X X' S S' : Scheme.{u}}

/-- Pushforward of a quasi-coherent module along an affine morphism commutes with arbitrary
cartesian base change. -/
@[stacks 02KG]
theorem affineBaseChange_pushforward_isomorphic
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) [IsAffineHom f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsIsomorphic
      (((Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj ℱ)) : S'.Modules)
      (((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj ℱ)) : S'.Modules) :=
  sorry

end AlgebraicGeometry.Scheme
