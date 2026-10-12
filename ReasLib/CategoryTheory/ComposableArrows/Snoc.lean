/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Snoc extension of finite composable arrows

This leaf owns the neutral, category-theoretic operation of appending one object and one
successor map to a finite `ComposableArrows` diagram.  It deliberately does not mention
homological properties; those belong in domain-specific leaves.  The object function and each
successor map are exposed separately so downstream constructions can reuse the computation API
without unpacking the implementation of `mkOfObjOfMapSucc`.
-/

noncomputable section

open CategoryTheory

universe v u

namespace CategoryTheory
namespace ComposableArrows

variable {C : Type u} [Category.{v} C]

/-- The object function obtained by appending `Y` to a finite composable-arrow diagram. -/
@[stacks 014M "object function for a snoc extension"]
def snocObj {n : ℕ} (F : ComposableArrows C n) (Y : C) : Fin (n + 2) → C :=
  Fin.lastCases Y (fun i ↦ F.obj i)

set_option linter.defProp false in
/-- The source object of an inherited successor map in a snoc extension. -/
@[stacks 014M "source computation for a snoc extension"]
def snocOldSourceEq {n : ℕ} (F : ComposableArrows C n) (Y : C) (i : Fin n) :
    snocObj F Y i.castSucc.castSucc = F.obj i.castSucc := by
  simp [snocObj]

set_option linter.defProp false in
/-- The target object of an inherited successor map in a snoc extension. -/
@[stacks 014M "target computation for a snoc extension"]
def snocOldTargetEq {n : ℕ} (F : ComposableArrows C n) (Y : C) (i : Fin n) :
    snocObj F Y i.castSucc.succ = F.obj i.succ := by
  rw [Fin.succ_castSucc, snocObj]
  simpa using
    (Fin.lastCases_castSucc
      (n := n + 1)
      (motive := fun _ : Fin (n + 2) ↦ C)
      (last := Y)
      (cast := fun j ↦ F.obj j)
      i.succ)

set_option linter.defProp false in
/-- The source object of the final successor map in a snoc extension. -/
@[stacks 014M "last-source computation for a snoc extension"]
def snocLastSourceEq {n : ℕ} (F : ComposableArrows C n) (Y : C) :
    snocObj F Y (Fin.last n).castSucc = F.right := by
  rw [snocObj, Fin.lastCases_castSucc]
  apply congrArg F.obj
  ext
  rfl

set_option linter.defProp false in
/-- The target object of the final successor map in a snoc extension. -/
@[stacks 014M "last-target computation for a snoc extension"]
def snocLastTargetEq {n : ℕ} (F : ComposableArrows C n) (Y : C) :
    snocObj F Y (Fin.last n).succ = Y := by
  simp [snocObj]

/-- An inherited successor map, transported across the object equalities of `snocObj`. -/
@[stacks 014M "inherited map in a snoc extension"]
def snocOldMap {n : ℕ} (F : ComposableArrows C n) (Y : C) (i : Fin n) :
    snocObj F Y i.castSucc.castSucc ⟶ snocObj F Y i.castSucc.succ :=
  eqToHom (snocOldSourceEq F Y i) ≫
    F.map' i.1 (i.1 + 1) ≫
      eqToHom (snocOldTargetEq F Y i).symm

/-- The final successor map in a snoc extension, transported across the endpoint equality. -/
@[stacks 014M "last map in a snoc extension"]
def snocLastMap {n : ℕ} (F : ComposableArrows C n) (Y : C) (f : F.right ⟶ Y) :
    snocObj F Y (Fin.last n).castSucc ⟶ snocObj F Y (Fin.last n).succ :=
  eqToHom (snocLastSourceEq F Y) ≫ f ≫ eqToHom (snocLastTargetEq F Y).symm

/-- The successor-map family used to build a snoc extension. -/
@[stacks 014M "successor-map family for a snoc extension"]
def snocMap {n : ℕ} (F : ComposableArrows C n) (Y : C) (f : F.right ⟶ Y) :
    ∀ i : Fin (n + 1), (snocObj F Y i.castSucc) ⟶ snocObj F Y i.succ :=
  Fin.lastCases (snocLastMap F Y f) (fun i ↦ snocOldMap F Y i)

/-- Append an object `Y` and a map `f : F.right ⟶ Y` to `F`. -/
@[stacks 014M "snoc extension of a finite composable-arrow diagram"]
def snoc {n : ℕ} (F : ComposableArrows C n) (Y : C) (f : F.right ⟶ Y) :
    ComposableArrows C (n + 1) :=
  ComposableArrows.mkOfObjOfMapSucc (snocObj F Y) (snocMap F Y f)

/-- The snoc extension agrees with the original diagram on the initial segment. -/
@[simp, stacks 014M "snoc object computation on the initial segment"]
theorem snoc_obj_castSucc {n : ℕ} (F : ComposableArrows C n) (Y : C)
    (f : F.right ⟶ Y) (i : Fin (n + 1)) :
    (snoc F Y f).obj i.castSucc = F.obj i := sorry

/-- The final object of a snoc extension is the appended object. -/
@[simp, stacks 014M "snoc final-object computation"]
theorem snoc_obj_last {n : ℕ} (F : ComposableArrows C n) (Y : C) (f : F.right ⟶ Y) :
    (snoc F Y f).obj (Fin.last (n + 1)) = Y := sorry

/-- The successor maps on the initial segment are the inherited maps. -/
@[simp, stacks 014M "snoc inherited-map computation"]
theorem snoc_map_castSucc {n : ℕ} (F : ComposableArrows C n) (Y : C)
    (f : F.right ⟶ Y) (i : Fin n) :
    (snoc F Y f).map' i.1 (i.1 + 1) = snocOldMap F Y i := sorry

/-- The final successor map of a snoc extension is the transported appended map. -/
@[simp, stacks 014M "snoc final-map computation"]
theorem snoc_map_last {n : ℕ} (F : ComposableArrows C n) (Y : C) (f : F.right ⟶ Y) :
    (snoc F Y f).map' n (n + 1) = snocLastMap F Y f := sorry

/-- Every successor map of a snoc extension is the corresponding member of `snocMap`. -/
@[simp, stacks 014M "snoc successor-map computation"]
theorem snoc_map_succ {n : ℕ} (F : ComposableArrows C n) (Y : C) (f : F.right ⟶ Y)
    (i : Fin (n + 1)) :
    (snoc F Y f).map' i.1 (i.1 + 1) = snocMap F Y f i := sorry

end ComposableArrows
end CategoryTheory
