/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger
import StacksCheckRecall

/-!
# Schlessinger's conditions (S1) and (S2)

Conditions (S1) and (S2) on a category cofibered in groupoids over `C_Λ` are the
diagram-completion properties `Functor.HasSchlessingerS1` and `Functor.HasSchlessingerS2`.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k)

/- Definition 90.10.1 (1): every cospan in `F` lying over `A1 ⟶ A ← A2` in
`ArtinianLocalAlgCat Λ k` with `A2 ⟶ A` surjective can be completed to a commutative
square lying over a fibre product `A1 ×_A A2`. -/
@[stacks 06HW]
#check (CategoryTheory.Functor.HasSchlessingerS1 p : Prop)

/- Definition 90.10.1 (2): the (S1) completion property for cospans over
`A ⟶ k ← DualNumber k`, together with existence of a fibre morphism `b : y ⟶ y'`
satisfying `b ≫ a' = a` between any two such completions. -/
@[stacks 06HW]
#check (CategoryTheory.Functor.HasSchlessingerS2 p : Prop)
