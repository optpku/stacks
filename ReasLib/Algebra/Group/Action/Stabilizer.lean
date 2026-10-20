/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Stabilizers under equivariant maps

This file isolates the group-action argument behind stabilizer surjectivity.  The target
group homomorphism is surjective, while a kernel correction inside the orbit fiber of the
chosen point lifts a target stabilizer element to a source stabilizer.
@stack 0BRJ
@stack 0BSX
-/

universe u v w z

namespace MulAction

variable {G : Type u} {X : Type v} [Group G] [MulAction G X]

/-- An element of a group belongs to the stabilizer of a point fixed by the whole group. -/
@[stacks 0BRJ "element of the stabilizer of a globally fixed point"]
def stabilizerOfFixed (x : X) (hfixed : ∀ g : G, g • x = x) (g : G) :
    MulAction.stabilizer G x :=
  ⟨g, hfixed g⟩

/-- The elements of a globally fixed point's stabilizer multiply as their ambient elements do. -/
@[stacks 0BRJ "multiplication in the stabilizer of a globally fixed point"]
theorem stabilizerOfFixed_mul (x : X) (hfixed : ∀ g : G, g • x = x) (g h : G) :
    stabilizerOfFixed x hfixed (g * h) =
      stabilizerOfFixed x hfixed g * stabilizerOfFixed x hfixed h := by
  apply Subtype.ext
  rfl
-- Proof strategy: apply `Subtype.ext`; both sides have ambient value `g * h` by construction.

/-- If every group element fixes `x`, the identity-on-elements map from the group to the
stabilizer of `x` is a group homomorphism. -/
@[stacks 0BRJ "homomorphism to the stabilizer of a globally fixed point"]
def stabilizerHomOfFixed (x : X) (hfixed : ∀ g : G, g • x = x) :
    G →* MulAction.stabilizer G x :=
  MonoidHom.mk' (stabilizerOfFixed x hfixed) (stabilizerOfFixed_mul x hfixed)

/-- The homomorphism to the stabilizer of a globally fixed point is the identity on ambient
group elements. -/
@[simp, stacks 0BRJ "globally fixed stabilizer homomorphism on elements"]
theorem stabilizerHomOfFixed_apply (x : X) (hfixed : ∀ g : G, g • x = x) (g : G) :
    ((stabilizerHomOfFixed x hfixed g : MulAction.stabilizer G x) : G) = g := by
  rfl
-- Proof strategy: unfold `stabilizerHomOfFixed`, `stabilizerOfFixed`, and `MonoidHom.mk'`; the
-- ambient value is definitionally `g`.

end MulAction

namespace Subgroup

variable {H : Type u} {G : Type v} {X : Type w} {Y : Type z}
variable [Group H] [Group G] [MulAction H X] [MulAction G Y]

/-- An equivariant surjection of acting groups maps a stabilizer onto the target stabilizer
when every point in the chosen orbit fiber can be corrected back by an element of the kernel. -/
@[stacks 0BSX "stabilizer image under a fiber-transitive equivariant map"]
theorem map_stabilizer_eq_of_surjective_of_fiber
    (f : H →* G) (p : X → Y) (x : X)
    (hsmul : ∀ h y, p (h • y) = f h • p y)
    (hf : Function.Surjective f)
    (hfiber : ∀ h : H, p (h • x) = p x → ∃ k : f.ker, k.1 • (h • x) = x) :
    Subgroup.map f (MulAction.stabilizer H x) = MulAction.stabilizer G (p x) := by
  apply le_antisymm
  · rintro _ ⟨h, hh, rfl⟩
    change f h • p x = p x
    rw [← hsmul, hh]
  · intro g hg
    obtain ⟨h, rfl⟩ := hf g
    have hp : p (h • x) = p x := by
      rw [hsmul]
      exact hg
    obtain ⟨k, hk⟩ := hfiber h hp
    refine ⟨k.1 * h, ?_, ?_⟩
    · change (k.1 * h) • x = x
      rw [mul_smul, hk]
    · rw [map_mul, k.property, one_mul]
-- Proof strategy: prove subgroup equality by extensionality.  The forward inclusion follows from
-- `hsmul`.  For the reverse inclusion, lift a target stabilizer element `g` to `h : H` using
-- `hf`; equivariance makes `p (h • x) = p x`, so `hfiber` gives `k : f.ker` correcting `h • x`
-- back to `x`.  Then `k.1 * h` stabilizes `x` and has image `g` because `f k = 1`.

end Subgroup
