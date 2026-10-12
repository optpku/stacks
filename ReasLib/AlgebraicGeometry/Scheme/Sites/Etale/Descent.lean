/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SheafPseudofunctor
public import Mathlib.AlgebraicGeometry.Morphisms.Integral

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.EtaleSheaf

/-- For a surjective integral morphism of schemes `f : X ⟶ Y`, canonical descent
along the singleton family `{f}` is an equivalence between Type-valued small
étale sheaves on `Y` and descent data on `X`. -/
theorem descentIsEquivalenceOfSurjectiveIntegral {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Surjective f] [IsIntegralHom f] :
    (pseudofunctor.toDescentData (fun _ : PUnit.{1} ↦ f)).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.EtaleSheaf
