/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Pushforward

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

universe v

/- Lemma 48.31.1 -/
@[stacks 0G4W]
#check (AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.extensionByZero_pushforwardIso :
  ∀ {X Y : Scheme.{v}} (f : X ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y]
    [IsProper f] (V : Y.Opens)
    [IsNoetherian V]
    [IsNoetherian (f ⁻¹ᵁ V)],
    AlgebraicGeometry.Scheme.ModuleDerived.properPushforward (f ∣_ V) ⋙
        AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.extensionByZero V.ι ≅
      AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.properPushforwardLim f (V := V))
