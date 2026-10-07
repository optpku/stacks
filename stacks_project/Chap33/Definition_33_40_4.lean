module

import StacksCheckRecall
public import ReasLib.RingTheory.LocalRing.Wedge.Basic

@[expose] public section

universe u v

/- Definition 33.40.4: a local ring is a wedge of a nonempty finite family of local rings when
some residue-field identifications make it isomorphic to their compatible-residue subring. -/
@[stacks 0C41] #check
  (LocalRing.Wedge.isWedgeOf_iff :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] {m : ℕ}
      (As : Fin (m + 1) → Type v) [∀ i, CommRing (As i)] [∀ i, IsLocalRing (As i)],
      LocalRing.Wedge.IsWedgeOf A As ↔
        ∃ residueFieldEquivToLast :
            ∀ i : Fin m,
              IsLocalRing.ResidueField (As i.castSucc) ≃+*
                IsLocalRing.ResidueField (As (Fin.last m)),
          Nonempty (A ≃+* LocalRing.Wedge.subring As residueFieldEquivToLast))
