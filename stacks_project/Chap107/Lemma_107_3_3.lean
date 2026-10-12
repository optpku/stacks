/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Irreducible
public import ReasLib.AlgebraicGeometry.Scheme.IrreducibleComponent.Multiplicity
public import stacks_project.Chap101.Definition_101_8_1_Noetherian
public import stacks_project.Chap101.Definition_101_13_2_Closed

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 107.3.3: if `f1 : U1 ⟶ X` and `f2 : U2 ⟶ X` are smooth morphisms from
schemes to a locally Noetherian algebraic stack, `T1'` and `T2'` are irreducible
components of `|U1|` and `|U2|` whose image-closures are the same irreducible
component `T` of `|X|`, then `U1.left.irreducibleComponentMultiplicity T1'` equals
`U2.left.irreducibleComponentMultiplicity T2'`. -/
@[stacks 0DR7]
theorem irreducibleComponentMultiplicity_eq_of_smooth
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]
    {U1 U2 : Over S} (f1 : GroupoidsOver.slice U1 ⟶ X) (f2 : GroupoidsOver.slice U2 ⟶ X)
    [Groupoids.Hom.Smooth f1] [Groupoids.Hom.Smooth f2]
    [AlgebraicGeometry.IsLocallyNoetherian U1.left]
    [AlgebraicGeometry.IsLocallyNoetherian U2.left]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    (T1' : irreducibleComponents U1.left) (T2' : irreducibleComponents U2.left)
    (T : @irreducibleComponents (Points X) τ)
    (h1 : @closure (Points X) τ (Set.image (Points.mapOfSlice f1) (T1' : Set U1.left)) =
      (T : Set (Points X)))
    (h2 : @closure (Points X) τ (Set.image (Points.mapOfSlice f2) (T2' : Set U2.left)) =
      (T : Set (Points X))) :
    U1.left.irreducibleComponentMultiplicity T1' =
      U2.left.irreducibleComponentMultiplicity T2' :=
  sorry

end AlgebraicGeometry.AlgebraicStack
