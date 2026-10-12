/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.FixedPoints
public import ReasLib.AlgebraicGeometry.MultiplicativeGroup.Powers
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Properties
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Exercise 111.65.6 (Fixed points)

Over an algebraically closed field, actions of multiplicative tori on projective
varieties have rational fixed points, while a connected group scheme may act on
a smooth projective variety with none.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.MultiplicativeGroup
open MonoidalCategory CartesianMonoidalCategory
open scoped AlgebraicGeometry CategoryTheory MonObj

noncomputable section

/- Exercise 111.65.6 (Fixed points) (1): every action of `𝔾ₘ` over an algebraically
closed field on a projective variety has a rational fixed point. -/
@[stacks 0GYE] #check (AlgebraicGeometry.GroupScheme.exists_fixedPoint_of_gm_action :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [ProjectiveVariety X] [ModObj (𝔾ₘ[Spec (CommRingCat.of k)]).X X],
    ∃ x : 𝟙_ (SchemeOverField k) ⟶ X,
      ∀ g : 𝟙_ (SchemeOverField k) ⟶ (𝔾ₘ[Spec (CommRingCat.of k)]).X,
        g • x = x)

/- Exercise 111.65.6 (Fixed points) (2): every action of a finite product of
𝔾ₘ on a projective variety over an algebraically closed field has a rational fixed point. -/
@[stacks 0GYE] #check (AlgebraicGeometry.GroupScheme.exists_fixedPoint_of_gmPow_action :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}, 1 ≤ n →
    (X : SchemeOverField k) → [ProjectiveVariety X] → [ModObj (pow k n) X] →
    ∃ x : 𝟙_ (SchemeOverField k) ⟶ X,
      ∀ g : 𝟙_ (SchemeOverField k) ⟶ pow k n, g • x = x)

/- Exercise 111.65.6 (Fixed points) (3): a connected group scheme can act on a
smooth projective variety without a rational fixed point. -/
@[stacks 0GYE] #check
  (AlgebraicGeometry.GroupScheme.exists_connected_action_without_fixedPoint :
    ∀ {k : Type u} [Field k] [IsAlgClosed k],
      ∃ (G X : SchemeOverField k) (hG : GrpObj G) (hX : ModObj G X),
        ConnectedSpace G.left ∧ SmoothVariety X ∧ ProjectiveVariety X ∧
          ¬ ∃ x : 𝟙_ (SchemeOverField k) ⟶ X,
              ∀ g : 𝟙_ (SchemeOverField k) ⟶ G, g • x = x)

#check AlgebraicGeometry.MultiplicativeGroup.pow
#check AlgebraicGeometry.MultiplicativeGroup.pow_zero
#check AlgebraicGeometry.MultiplicativeGroup.pow_succ
