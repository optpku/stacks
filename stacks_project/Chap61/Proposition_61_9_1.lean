module

public import ReasLib.RingTheory.RingHom.IndEtale.Refinement
import StacksCheckRecall

/-!
# Proposition 61.9.1

A weakly étale ring map admits a faithfully flat ind-étale extension whose
composite is ind-étale.
-/

@[expose] public section

universe u

/- Proposition 61.9.1: a weakly étale ring map admits a faithfully flat,
ind-étale extension whose composite is ind-étale. -/
@[stacks 097Z] #check
  (RingHom.IndEtale.exists_faithfullyFlat_of_weaklyEtale :
    ∀ {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B},
      f.WeaklyEtale → ∃ (B' : Type u) (_ : CommRing B') (g : B →+* B'),
        g.FaithfullyFlat ∧ g.IndEtale ∧ (g.comp f).IndEtale)
