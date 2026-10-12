/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType.Neighborhood
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 17.9.4 (01B8): stalkwise surjectivity into a finite-type module sheaf holds on some
open neighborhood. -/
@[stacks 01B8]
#check fun {X : RingedSpace.{u}} {G F : X.Modules} (φ : G ⟶ F) (x : X)
    [F.IsFiniteType] (hφx : Function.Surjective (RingedSpace.moduleStalkMap x φ)) ↦
  SheafOfModules.IsFiniteType.existsNeighborhood_epi_of_surjective
    φ x hφx
