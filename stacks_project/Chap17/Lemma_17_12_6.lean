/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Neighborhood
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 17.12.6 (01C0): a map from a finite-type module sheaf to a coherent one which is
injective at a stalk becomes a monomorphism after restricting to some neighborhood. -/
@[stacks 01C0]
#check fun {X : RingedSpace.{u}} {G F : X.Modules} (φ : G ⟶ F) (x : X)
    [G.IsFiniteType] [F.IsCoherent]
    (hφx : Function.Injective (RingedSpace.moduleStalkMap x φ)) ↦
  SheafOfModules.Hom.existsNeighborhood_mono_of_injective
    φ x hφx
