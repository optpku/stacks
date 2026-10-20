/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.MilnorTriangle
public import ReasLib.CategoryTheory.Pro.Sequential.Isomorphism
public import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived limits and pro-isomorphisms

This leaf owns the invariant form of the non-canonical uniqueness statement for sequential
derived limits.  The public hypothesis is a morphism in the pro-category; a monotone level
representative is implementation data and is intentionally absent from the theorem surface.
@stack 0H9L
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

noncomputable section

universe u v

namespace CategoryTheory.IsDerivedLimit

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor D n)]
  [Pretriangulated D] [IsTriangulated D]

/-- Lemma 15.87.6 (Stacks 0H9L): a pro-isomorphism between two sequential systems induces a
non-canonical isomorphism between any chosen derived limits of those systems. -/
@[stacks 0H9L]
theorem existsIso_of_proIso
    {Ksys Msys : SequentialInverseSystem D} {K M : D}
    (hK : IsDerivedLimit Ksys K) (hM : IsDerivedLimit Msys M)
    (η : (Pro.lim (C := D) ℕᵒᵖ).obj Ksys ⟶
      (Pro.lim (C := D) ℕᵒᵖ).obj Msys) [IsIso η] :
    ∃ f : K ⟶ M, IsIso f := sorry

/-- A pro-isomorphism between sequential systems makes any two chosen derived limits
noncanonically isomorphic. -/
@[stacks 0H9L]
theorem nonemptyIso_of_proIso
    {Ksys Msys : SequentialInverseSystem D} {K M : D}
    (hK : IsDerivedLimit Ksys K) (hM : IsDerivedLimit Msys M)
    (η : (Pro.lim (C := D) ℕᵒᵖ).obj Ksys ⟶
      (Pro.lim (C := D) ℕᵒᵖ).obj Msys) [IsIso η] :
    Nonempty (K ≅ M) := sorry

/-- A representative inverse between sequential presentations induces a non-canonical
isomorphism between any chosen derived limits. -/
@[stacks 0GZI]
theorem existsIso_of_hasRepresentativeInverse
    {Ksys Msys : SequentialInverseSystem D} {K M : D}
    (hK : IsDerivedLimit Ksys K) (hM : IsDerivedLimit Msys M)
    (r : Pro.SequentialHom Ksys Msys) (hr : r.HasRepresentativeInverse) :
    ∃ f : K ⟶ M, IsIso f := sorry

/-- A representative inverse between sequential presentations makes any two chosen derived
limits noncanonically isomorphic. -/
@[stacks 0GZI]
theorem nonemptyIso_of_hasRepresentativeInverse
    {Ksys Msys : SequentialInverseSystem D} {K M : D}
    (hK : IsDerivedLimit Ksys K) (hM : IsDerivedLimit Msys M)
    (r : Pro.SequentialHom Ksys Msys) (hr : r.HasRepresentativeInverse) :
    Nonempty (K ≅ M) := sorry

end CategoryTheory.IsDerivedLimit

end
