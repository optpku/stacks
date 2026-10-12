/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.FiniteConnected.Preserves
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Finite connected colimits in coslice categories

Connected colimits in a coslice are created by its forgetful functor. Consequently the semantic
finite-connected-colimit owner transfers from an ambient category to every coslice category.
-/

@[expose] public section

open CategoryTheory.Limits

universe u v

namespace CategoryTheory.Under

variable {C : Type u} [Category.{v} C]

/-- A coslice category has finite connected colimits whenever its ambient category does. -/
instance (priority := 100) hasFiniteConnectedColimits [HasFiniteConnectedColimits C] (X : C) :
    HasFiniteConnectedColimits (Under X) := sorry

/-- The forgetful functor from a coslice category preserves all finite connected colimits. -/
instance (priority := 100) Forget.preservesFiniteConnectedColimits (X : C) :
    PreservesFiniteConnectedColimits (Under.forget X) := sorry

/-- Precomposition between coslice categories preserves all finite connected colimits. -/
instance (priority := 100) Map.preservesFiniteConnectedColimits
    {X Y : C} (f : X ⟶ Y) :
    PreservesFiniteConnectedColimits (Under.map f) := sorry

end CategoryTheory.Under

section AggregateSynthesis

variable {C : Type u} [CategoryTheory.Category.{v} C] [HasFiniteConnectedColimits C]
variable {X Y : C} (f : X ⟶ Y)

#synth HasFiniteConnectedColimits (CategoryTheory.Under X)
#synth PreservesFiniteConnectedColimits (CategoryTheory.Under.forget X)
#synth PreservesFiniteConnectedColimits (CategoryTheory.Under.map f)

end AggregateSynthesis
