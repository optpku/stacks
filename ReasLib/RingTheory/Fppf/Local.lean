module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.FinitePresentation

@[expose] public section

universe u

/-- A commutative ring is fppf-local when it is local and every faithfully flat,
finitely presented extension admits a retraction. -/
def IsFppfLocalRing (B : Type u) [CommRing B] : Prop :=
  IsLocalRing B ∧
    (∀ (B' : Type u) [CommRing B'] (g : B →+* B'),
      g.FaithfullyFlat → g.FinitePresentation →
        ∃ r : B' →+* B, r.comp g = RingHom.id B)

end
