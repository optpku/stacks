/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Section-normalization design compared with TauCetiProject/TauCeti,
commit 76eb167bacad4b75ea1cb657b4db1d7efb788022,
AlgebraicGeometry/PicardFunctor/Relative.lean (Apache-2.0).
Extracted from ReasLib's relative Picard normalization into its additive-group owner.
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Tactic.Abel

/-!
# Quotient by the image of a split injection

For additive homomorphisms `i : A →+ B` and `r : B →+ A` satisfying
`r (i a) = a`, `QuotientAddGroup.quotientRangeEquivKer` identifies
`B ⧸ i.range` with `r.ker`. It sends the class of `b` to `b - i (r b)`;
the inverse is the quotient map restricted to the kernel.

The ambient group `B` is commutative. The retract `A` only needs an
`AddGroup` instance. The construction uses Mathlib's existing quotient,
kernel, and additive equivalence, with no extra splitting structure.
It applies to split additive extensions and to the additive groups of
split module maps, as well as to section pullbacks of Picard groups.
-/

@[expose] public section

namespace QuotientAddGroup

variable {A B : Type*} [AddGroup A] [AddCommGroup B]
    (i : A →+ B) (r : B →+ A) (h : Function.LeftInverse r i)

/-- Quotient by the image of a section is the kernel of its retraction.
The representative of the class of `b` is `b - i (r b)`. -/
def quotientRangeEquivKer : B ⧸ i.range ≃+ r.ker := by
  let n : B →+ r.ker :=
    { toFun := fun b ↦ ⟨b - i (r b), by
        change r (b - i (r b)) = 0
        rw [map_sub, h, sub_self]⟩
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := by
        intro b c
        apply Subtype.ext
        change (b + c) - i (r (b + c)) = (b - i (r b)) + (c - i (r c))
        simp only [map_add]
        abel }
  let q : B ⧸ i.range →+ r.ker := lift i.range n (by
    rintro b ⟨a, rfl⟩
    apply Subtype.ext
    change i a - i (r (i a)) = 0
    rw [h, sub_self])
  exact
    { q with
      invFun := fun b ↦ mk b.1
      left_inv := by
        intro b
        obtain ⟨b, rfl⟩ := mk_surjective b
        apply eq_iff_sub_mem.mpr
        refine ⟨-r b, ?_⟩
        change i (-r b) = (b - i (r b)) - b
        rw [map_neg]
        abel
      right_inv := by
        intro b
        apply Subtype.ext
        change b.1 - i (r b.1) = b.1
        rw [show r b.1 = 0 from b.2, map_zero, sub_zero] }

/-- The explicit normalization formula on representatives. -/
@[simp]
theorem quotientRangeEquivKer_mk (b : B) :
    (quotientRangeEquivKer i r h (mk b)).1 = b - i (r b) := rfl

/-- Forgetting the normalization returns the quotient class of the kernel element. -/
@[simp]
theorem quotientRangeEquivKer_symm_apply (b : r.ker) :
    (quotientRangeEquivKer i r h).symm b = mk b.1 := rfl

/-- Normalization commutes with homomorphisms that respect the section and retraction.
The map on quotients is Mathlib's `QuotientAddGroup.map`. -/
theorem quotientRangeEquivKer_natural
    {A' B' : Type*} [AddGroup A'] [AddCommGroup B']
    (i' : A' →+ B') (r' : B' →+ A') (h' : Function.LeftInverse r' i')
    (f : A →+ A') (g : B →+ B')
    (hi : ∀ a, g (i a) = i' (f a)) (hr : ∀ b, r' (g b) = f (r b))
    (q : B ⧸ i.range) :
    (quotientRangeEquivKer i' r' h'
      (map i.range i'.range g (by
        rintro b ⟨a, rfl⟩
        exact ⟨f a, (hi a).symm⟩) q)).1 =
      g (quotientRangeEquivKer i r h q).1 := by
  refine Quotient.inductionOn' q ?_
  intro b
  simp only [map_mk, quotientRangeEquivKer_mk, map_sub, hi, hr]

end QuotientAddGroup
