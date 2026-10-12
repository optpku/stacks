/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import StacksCheckRecall

@[expose] public section

open CategoryTheory SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/- The project-local ringed-space functors are direct specializations of
`SheafOfModules.pushforward` and `SheafOfModules.pullback`. Their composition laws should therefore
remain views of the canonical owners: pushforward composition is definitional, while pullback
composition uses `SheafOfModules.pullbackComp`. This avoids a parallel ringed-space comparison API
and keeps the exact source equality in the clause where it is available. -/

/- Lemma 6.26.3 (1): for morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z`, the
pushforward functor along the composite equals the composite of the two pushforward functors. -/
@[stacks 0097 "pushforward composition for module sheaves on ringed spaces"]
#check (rfl : (f ≫ g) _* = f _* ⋙ g _*)

/- Lemma 6.26.3 (2): for morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z`, the
pullback along the composite is canonically isomorphic to the composite pullback functor
`f^* ∘ g^*`. -/
@[stacks 0097 "pullback composition for module sheaves on ringed spaces"]
#check
  ((pullbackComp
      (RingedSpace.Hom.toRingCatSheafHom g)
      (RingedSpace.Hom.toRingCatSheafHom f)).symm :
    (f ≫ g)^* ≅ g^* ⋙ f^*)

end

end AlgebraicGeometry
