/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap110.Proposition_110_77_1_Torsion
public import stacks_project.Chap110.Proposition_110_77_1_Equivalence
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

namespace ModuleCat

variable {R : Type u} [CommRing R] [Small.{v} R] (S : Submonoid R)

/- Proposition 110.77.1: the Serre quotient of `ModuleCat A` by the `S`-torsion modules is
canonically equivalent to `ModuleCat (Localization S)`, via the induced functor of
localization `M ↦ S⁻¹M ≅ M ⊗[A] Localization S`. -/
@[stacks 0EA5]
#check (inducedLocalizedFunctor_isEquivalence S :
  (inducedLocalizedFunctor S).IsEquivalence)

end ModuleCat
