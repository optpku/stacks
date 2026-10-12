/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.AlgebraicTopology.DoldKan.FunctorGamma
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Single.Functor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Eilenberg-MacLane simplicial-object functor

The canonical owner of `K(B, k)` is the Dold-Kan image of the chain complex concentrated in
degree `k`.  Comparison results with truncations, skeletons, and normalized Moore complexes live
in separate leaf modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject

namespace eilenbergMacLane

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasZeroObject A]
  [HasFiniteCoproducts A]

/-- For fixed `k`, the Eilenberg-MacLane construction is the composite of the single-complex
functor in degree `k` with the explicit coproduct model of the inverse Dold-Kan functor. -/
@[stacks 0191 "Eilenberg-MacLane functor"]
noncomputable abbrev functor (k : ℕ) : A ⥤ SimplicialObject A :=
  single A (ComplexShape.down ℕ) k ⋙ AlgebraicTopology.DoldKan.Γ₀

end eilenbergMacLane

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasZeroObject A]
  [HasFiniteCoproducts A]

/-- The Eilenberg-MacLane simplicial object `K(B, k)`, owned as the value of the functorial
Dold-Kan construction in degree `k`. -/
@[stacks 0191 "Eilenberg-MacLane simplicial object"]
noncomputable abbrev eilenbergMacLane (B : A) (k : ℕ) : SimplicialObject A :=
  (eilenbergMacLane.functor (A := A) k).obj B

/-- Textbook notation for the Eilenberg-MacLane simplicial object. -/
scoped[Simplicial] notation:max "K(" B ", " k ")" => SimplicialObject.eilenbergMacLane B k

namespace eilenbergMacLane

/-- Evaluating the Eilenberg-MacLane functor gives the canonical object `K(X, k)`. -/
@[simp, stacks 0191 "Eilenberg-MacLane functor object formula"]
theorem functor_obj (k : ℕ) (X : A) :
    (functor (A := A) k).obj X = eilenbergMacLane X k := sorry

/-- The Eilenberg-MacLane functor maps a morphism by first placing it in a single complex and
then applying the inverse Dold-Kan functor. -/
@[simp, stacks 0191 "Eilenberg-MacLane functor map formula"]
theorem functor_map (k : ℕ) {X Y : A} (f : X ⟶ Y) :
    (functor (A := A) k).map f =
      AlgebraicTopology.DoldKan.Γ₀.map
        ((single A (ComplexShape.down ℕ) k).map f) := sorry

end eilenbergMacLane

end CategoryTheory.SimplicialObject
