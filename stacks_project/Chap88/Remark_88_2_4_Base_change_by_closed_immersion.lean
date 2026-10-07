module

public import Mathlib.CategoryTheory.NatIso
public import stacks_project.Chap88.Remark_88_2_4_Base_change_by_closed_immersion_Quotient

/-!
# Base change by a closed immersion

The completed base-change functor of 88.2.3.2 along `A → A ⧸ a` is naturally
isomorphic to the quotient functor `B ↦ B ⧸ aB` on `C'`.
-/

@[expose] public section

open CategoryTheory

universe u

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

namespace CommAlgCat.TopologicallyFiniteType

/-- Remark 88.2.4 (Base change by closed immersion). Let `A` be a Noetherian
ring and `I ⊂ A` an ideal. Let `a ⊂ A` be an ideal. Denote `Ā = A ⧸ a`. Let
`Ī ⊂ Ā` be an ideal such that `I ^ c Ā ≤ Ī` and `Ī ^ d ≤ I Ā` for some
`c, d ≥ 1`. In this case the base change functor of 88.2.3.2 for `(A, I)` to
`(Ā, Ī)` is given by `B ↦ B ⧸ aB`. -/
@[stacks 0AL6]
noncomputable def closedImmersionBaseChangeIso (I a : Ideal A) (Ibar : Ideal (A ⧸ a))
    {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hI : I.map (algebraMap A (A ⧸ a)) ^ c ≤ Ibar)
    (hIbar : Ibar ^ d ≤ I.map (algebraMap A (A ⧸ a))) :
    baseChange I Ibar hc hI (IsNoetherian.noetherian Ibar) ≅
      quotIdeal I a Ibar hc hd hI hIbar :=
  NatIso.ofComponents (isoComponent I a Ibar hc hd hI hIbar) sorry

/-- Components of `closedImmersionBaseChangeIso` are the objectwise identifications
`isoComponent`. -/
theorem closedImmersionBaseChangeIso_app (I a : Ideal A) (Ibar : Ideal (A ⧸ a))
    {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hI : I.map (algebraMap A (A ⧸ a)) ^ c ≤ Ibar)
    (hIbar : Ibar ^ d ≤ I.map (algebraMap A (A ⧸ a)))
    (B : TopologicallyFiniteType.{u} A I) :
    (closedImmersionBaseChangeIso I a Ibar hc hd hI hIbar).app B =
      isoComponent I a Ibar hc hd hI hIbar B := sorry

end CommAlgCat.TopologicallyFiniteType
