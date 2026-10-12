/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.MultiplicativeGroup.Powers
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Properties

/-!
# Fixed points of group-scheme actions
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.MultiplicativeGroup
open MonoidalCategory CartesianMonoidalCategory
open scoped AlgebraicGeometry CategoryTheory MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupScheme

/-- Over an algebraically closed field `k`, every action of `𝔾ₘ` over `k` on a
projective variety `X` has a `k`-rational fixed point. -/
theorem exists_fixedPoint_of_gm_action {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [ProjectiveVariety X]
    [ModObj (𝔾ₘ[Spec (CommRingCat.of k)]).X X] :
    ∃ x : 𝟙_ (SchemeOverField k) ⟶ X,
      ∀ g : 𝟙_ (SchemeOverField k) ⟶ (𝔾ₘ[Spec (CommRingCat.of k)]).X,
        g • x = x := sorry

/-- The existence of a rational fixed point for a `𝔾ₘ`-action is the nonemptiness
of the fixed-point set of the induced action on `k`-points. -/
theorem exists_fixedPoint_of_gm_action_iff {k : Type u} [Field k]
    (X : SchemeOverField k) [ModObj (𝔾ₘ[Spec (CommRingCat.of k)]).X X] :
    (∃ x : 𝟙_ (SchemeOverField k) ⟶ X,
        ∀ g : 𝟙_ (SchemeOverField k) ⟶ (𝔾ₘ[Spec (CommRingCat.of k)]).X,
          g • x = x) ↔
      (MulAction.fixedPoints
          (𝟙_ (SchemeOverField k) ⟶ (𝔾ₘ[Spec (CommRingCat.of k)]).X)
          (𝟙_ (SchemeOverField k) ⟶ X)).Nonempty := sorry

/-- Over an algebraically closed field `k`, every action of an `n`-fold product
of `𝔾ₘ` with `1 ≤ n` on a projective variety `X` has a `k`-rational fixed point. -/
theorem exists_fixedPoint_of_gmPow_action {k : Type u} [Field k] [IsAlgClosed k]
    {n : ℕ} (hn : 1 ≤ n) (X : SchemeOverField k) [ProjectiveVariety X]
    [ModObj (pow k n) X] :
    ∃ x : 𝟙_ (SchemeOverField k) ⟶ X,
      ∀ g : 𝟙_ (SchemeOverField k) ⟶ pow k n, g • x = x := sorry

/-- The existence of a rational fixed point for a torus action is the nonemptiness
of the fixed-point set of the induced action on `k`-points. -/
theorem exists_fixedPoint_of_gmPow_action_iff {k : Type u} [Field k] {n : ℕ}
    (X : SchemeOverField k) [ModObj (pow k n) X] :
    (∃ x : 𝟙_ (SchemeOverField k) ⟶ X,
        ∀ g : 𝟙_ (SchemeOverField k) ⟶ pow k n, g • x = x) ↔
      (MulAction.fixedPoints (𝟙_ (SchemeOverField k) ⟶ pow k n)
          (𝟙_ (SchemeOverField k) ⟶ X)).Nonempty := sorry

/-- There exist a connected group scheme over an algebraically closed field `k`
and an action on a smooth projective variety over `k` with no `k`-rational fixed point. -/
theorem exists_connected_action_without_fixedPoint {k : Type u} [Field k]
    [IsAlgClosed k] :
    ∃ (G X : SchemeOverField k) (hG : GrpObj G) (hX : ModObj G X),
      ConnectedSpace G.left ∧ SmoothVariety X ∧ ProjectiveVariety X ∧
        ¬ ∃ x : 𝟙_ (SchemeOverField k) ⟶ X,
            ∀ g : 𝟙_ (SchemeOverField k) ⟶ G, g • x = x := sorry

end AlgebraicGeometry.GroupScheme
