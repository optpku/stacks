/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent.Adjunction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)

variable [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]

/- Proposition 104.6.1 (1): derived direct image commutes with the inclusion
of bounded-below parasitic coefficient objects into bounded-below coefficient objects. -/
@[stacks 07BC] #check
  (AlgebraicGeometry.AlgebraicStack.derivedPushforwardPlusParasitic_comp_inclusion f :
    derivedPushforwardPlusParasitic f ⋙ derivedParasiticLQCohFbcPlus.inclusion Y ≅
      derivedParasiticLQCohFbcPlus.inclusion X ⋙ derivedPushforwardPlusLQCohFbc f)

/- Proposition 104.6.1 (2): derived direct image commutes with inclusion of
bounded-below coefficient objects into the unbounded module-derived category. -/
@[stacks 07BC] #check
  (AlgebraicGeometry.AlgebraicStack.derivedPushforwardPlusLQCohFbc_comp_ambient f :
    derivedPushforwardPlusLQCohFbc f ⋙ DerivedLQCohFbc.Plus.ambient Y ≅
      DerivedLQCohFbc.Plus.ambient X ⋙ moduleDerivedPushforward f)

/- Proposition 104.6.1 (3): derived direct image descends to the bounded-below
quasi-coherent Verdier quotient. -/
@[stacks 07BC] #check
  (AlgebraicGeometry.AlgebraicStack.DerivedQCoh.pushforward f :
    DerivedQCoh.Plus X ⥤ DerivedQCoh.Plus Y)

/- Proposition 104.6.1 (4): on quasi-coherent modules placed in degree zero,
the degree-i cohomology of derived direct image is quasi-coherent higher direct image. -/
@[stacks 07BC] #check
  (AlgebraicGeometry.AlgebraicStack.DerivedQCoh.cohomology_pushforward_single_iso f :
    ∀ i : ℕ, DerivedQCoh.singlePlus X ⋙ DerivedQCoh.pushforward f ⋙
      DerivedQCoh.Plus.inclusion Y ⋙ DerivedQCoh.cohomologyFunctor Y (i : ℤ) ≅
        QCoh.higherDirectImageFunctor f i)

end AlgebraicGeometry.AlgebraicStack
