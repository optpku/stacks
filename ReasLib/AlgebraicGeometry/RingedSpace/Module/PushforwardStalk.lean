/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sheaves.LocallySurjective
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalk maps and module pushforward

This file records the stalk bridge that depends only on an inducing underlying map and local
surjectivity of the structure-sheaf map. It therefore belongs to general pushforward
infrastructure rather than to closed immersions.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

variable {X Z : RingedSpace.{u}}

/-- Along an inducing ringed-space morphism, local surjectivity of `𝒪_X ⟶ i_* 𝒪_Z` implies
surjectivity of every induced source stalk map. -/
@[stacks 01C4 "stalk bridge"]
theorem stalkMap_surjective_of_isInducing
    (i : Z ⟶ X) (hi : Topology.IsInducing i.hom.base)
    [Sheaf.IsLocallySurjective (commRingSheafPushforwardMap i)] (z : Z) :
    Function.Surjective (PresheafedSpace.Hom.stalkMap i.hom z).hom := sorry

end AlgebraicGeometry.RingedSpace.Hom
