/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteType.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 35.7.9: for a finite morphism of schemes, a quasi-coherent module is of finite
type if and only if its pushforward is of finite type. -/
@[stacks 05B3] #check
  (AlgebraicGeometry.Scheme.Modules.isFiniteType_iff_pushforward_of_isFinite :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      ℱ.IsFiniteType ↔ ((Scheme.Modules.pushforward f).obj ℱ).IsFiniteType)
