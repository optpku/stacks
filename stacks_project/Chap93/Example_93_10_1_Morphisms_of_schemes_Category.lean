/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SchemeMorphism
import StacksCheckRecall

/-!
# Category of morphisms of schemes flat over Artinian local algebras

The category of flat scheme morphisms, its cartesian morphisms, and its residue
slice are provided by the shared mathematical owner.
-/

@[expose] public section

open CategoryTheory

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Example 93.10.1 (Morphisms of schemes)
The category of flat scheme morphisms over Artinian local algebras uses
cartesian morphisms with reversed scheme maps. -/
@[stacks 0E3T]
#check (FlatSchemeMorphismCat.category (Λ := Λ) (k := k) :
  Category.{u} (FlatSchemeMorphismCat Λ k))
