/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.LowerShriek
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits

universe u

/- Lemma 75.10.6. For étale `j : U ⟶ X` and `v : V ⟶ X`, restriction of derived
extension by zero is extension by zero of the restricted complex on `V ×_X U`.
The source writes `V ⟶ Y`; its fibre product and restriction force `V ⟶ X`. -/
@[stacks 08HA] #check (AlgebraicGeometry.AlgebraicSpace.Modules.restrictLowerShriekIso :
  ∀ {S : Scheme.{u}} {U X V : AlgebraicSpace S} (j : U ⟶ X) [Etale j]
    (v : V ⟶ X) [Etale v] (E : ModuleDerived U),
    (restrictFunctorDerived v).obj ((lowerShriekDerived j).obj E) ≅
      (lowerShriekDerived (Limits.pullback.fst v j)).obj
        ((restrictFunctorDerived (Limits.pullback.snd v j)).obj E))
