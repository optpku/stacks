module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.FormalObjectSystem
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

/-!
# Strong effectiveness of inverse systems of objects

A compatible system of objects over spectra of a sequential inverse system of
algebras is effective when it arises by restriction from an object over the
spectrum of the inverse limit.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.StrongEffectiveness

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S)}

abbrev System (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S)) :=
  AlgebraicGeometry.FormalObjectSystem X.p

/- Remark 98.20.2 (Strong effectiveness) -/
@[stacks 0CXT] #check (AlgebraicGeometry.FormalObjectSystem.IsEffective : System X → Prop)

end AlgebraicGeometry.GroupoidsOver.StrongEffectiveness
