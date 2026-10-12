/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.KanExtension.Pointwise
public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.Finite
public import ReasLib.CategoryTheory.Limits.FiniteConnected.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Truncated
import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 018N

# Truncated-simplex Kan extensions from finite connected (co)limits

For a positive truncation level, every structured-arrow category used by the coskeleton is finite
and connected. This file exposes the resulting pointwise right-Kan-extension instance so that
coskeletons elaborate without proof-local instance installation. Every costructured-arrow
category used by a skeleton has a canonical initial object in every truncation level, so finite
connected colimits suffice for all pointwise skeletons.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v

namespace SimplexCategory.Truncated

variable {C : Type u} [Category.{v} C] {k : ℕ}

namespace inclusion

namespace costructuredArrow

/-- The canonical initial object of a skeleton indexing category, represented by the unique map
from the target simplex to the zero simplex. -/
@[stacks 018N "initial skeleton indexing object"]
def initial (m : ℕ) (Delta : SimplexCategory) :
    CostructuredArrow (inclusion m).op (op Delta) :=
  objEquiv.forward
    ⟨op ⦋0, Nat.zero_le m⦌ₘ,
      ((SimplexCategory.const Delta ⦋0⦌ 0).op :
        (inclusion m).op.obj (op ⦋0, Nat.zero_le m⦌ₘ) ⟶ op Delta)⟩

/-- The underlying truncated-simplex morphism from the canonical zero-simplex object to an
arbitrary skeleton indexing object. -/
@[stacks 018N "initial skeleton indexing morphism"]
def initial.map {m : ℕ} {Delta : SimplexCategory}
    (A : CostructuredArrow (inclusion m).op (op Delta)) :
    (initial m Delta).left ⟶ A.left :=
  (ObjectProperty.homMk
    (SimplexCategory.const A.left.unop.obj ⦋0⦌ 0)).op

/-- The canonical underlying morphism satisfies the costructured-arrow triangle. -/
@[stacks 018N "initial skeleton indexing morphism condition"]
theorem initial.map_condition {m : ℕ} {Delta : SimplexCategory}
    (A : CostructuredArrow (inclusion m).op (op Delta)) :
    (inclusion m).op.map (initial.map A) ≫ A.hom = (initial m Delta).hom := sorry

/-- The canonical morphism from the initial skeleton indexing object to any indexing object. -/
@[stacks 018N "initial skeleton indexing arrow"]
def initial.to {m : ℕ} {Delta : SimplexCategory}
    (A : CostructuredArrow (inclusion m).op (op Delta)) :
    initial m Delta ⟶ A :=
  CostructuredArrow.homMk (initial.map A) (initial.map_condition A)

/-- The underlying morphism of the canonical arrow is the explicit constant map. -/
@[simp, stacks 018N "underlying initial skeleton indexing arrow"]
theorem initial.to_left {m : ℕ} {Delta : SimplexCategory}
    (A : CostructuredArrow (inclusion m).op (op Delta)) :
    (initial.to A).left = initial.map A := sorry

/-- Every morphism out of the canonical skeleton indexing object is the canonical one. -/
@[stacks 018N "uniqueness of the initial skeleton indexing arrow"]
theorem initial.to_unique {m : ℕ} {Delta : SimplexCategory}
    (A : CostructuredArrow (inclusion m).op (op Delta))
    (f : initial m Delta ⟶ A) :
    f = initial.to A := sorry

/-- The canonical zero-simplex object is initial in the skeleton indexing category. -/
@[stacks 018N "initiality of the skeleton indexing object"]
def initial.isInitial (m : ℕ) (Delta : SimplexCategory) :
    IsInitial (initial m Delta) :=
  IsInitial.ofUniqueHom initial.to initial.to_unique

/-- Every skeleton costructured-arrow category is connected. -/
@[stacks 018N "connected skeleton indexing category"]
instance isConnected (m : ℕ) (Delta : SimplexCategory) :
    IsConnected (CostructuredArrow (inclusion m).op (op Delta)) :=
  isConnected_of_isInitial _ (initial.isInitial m Delta)

end costructuredArrow

namespace finiteConnected

namespace pointwise

namespace right

/-- Remark 14.19.11 (2) (09VS): positive truncated-simplex inclusions admit pointwise right Kan
extensions in every category with finite connected limits. -/
@[stacks 09VS "positive coskeletons from finite connected limits"]
noncomputable instance (priority := 100)
    kanExtension
    [NeZero k] [HasFiniteConnectedLimits C]
    (F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ C) :
    (inclusion k).op.HasPointwiseRightKanExtension F :=
  fun ⟨⟨_⟩⟩ ↦ inferInstance

end right

namespace left

/-- Truncated-simplex inclusions admit pointwise left Kan extensions in every category with
finite connected colimits. -/
@[stacks 018N "skeletons from finite connected colimits"]
noncomputable instance (priority := 100)
    kanExtension
    [HasFiniteConnectedColimits C]
    (F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ C) :
    (inclusion k).op.HasPointwiseLeftKanExtension F :=
  fun ⟨⟨_⟩⟩ ↦ inferInstance

end left

end pointwise

namespace pointwise.right

/-- The explicit positivity bridge to the pointwise right-Kan-extension instance. -/
@[stacks 09VS "positive coskeleton positivity bridge"]
theorem of_pos
    (k : ℕ) (hk : 0 < k) [HasFiniteConnectedLimits C]
    (F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ C) :
    (inclusion k).op.HasPointwiseRightKanExtension F := sorry

end pointwise.right

end finiteConnected
end inclusion

end SimplexCategory.Truncated
