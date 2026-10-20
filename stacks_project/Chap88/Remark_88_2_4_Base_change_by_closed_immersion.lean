module

import StacksCheckRecall
public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType.ClosedImmersion

open CategoryTheory

universe u

/- Remark 88.2.4 (Base change by closed immersion). For a Noetherian ring `A`,
ideals `I` and `a`, and an ideal `Ibar` cofinal with the image of `I` in `A ⧸ a`,
completed tensor base change is naturally isomorphic to `B ↦ B ⧸ aB`. -/
@[stacks 0AL6] #check
  (CommAlgCat.TopologicallyFiniteType.closedImmersionBaseChangeIso :
    {A : Type u} → [CommRing A] → [IsNoetherianRing A] →
    (I a : Ideal A) → (Ibar : Ideal (A ⧸ a)) →
    {c d : ℕ} → (hc : 1 ≤ c) → (hd : 1 ≤ d) →
    (hI : I.map (algebraMap A (A ⧸ a)) ^ c ≤ Ibar) →
    (hIbar : Ibar ^ d ≤ I.map (algebraMap A (A ⧸ a))) →
    CommAlgCat.TopologicallyFiniteType.baseChange I Ibar hc hI
        (IsNoetherian.noetherian Ibar) ≅
      CommAlgCat.TopologicallyFiniteType.quotIdeal I a Ibar hc hd hI hIbar)
