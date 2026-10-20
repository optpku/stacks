module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import ReasLib.RingTheory.RingHom.IndEtale.Basic
public import ReasLib.RingTheory.RingHom.WeaklyEtale

/-!
# Ind-étale refinement of weakly étale ring maps

A weakly étale ring map admits a faithfully flat ind-étale extension whose
composite is ind-étale.
-/

@[expose] public section

universe u

namespace RingHom.IndEtale

/-- If `f : A →+* B` is weakly étale, then there exists a faithfully flat,
ind-étale ring map `g : B →+* B'` such that `g.comp f` is ind-étale. -/
@[stacks 097Z]
theorem exists_faithfullyFlat_of_weaklyEtale
    {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}
    (hf : f.WeaklyEtale) :
    ∃ (B' : Type u) (_ : CommRing B') (g : B →+* B'),
      g.FaithfullyFlat ∧ g.IndEtale ∧ (g.comp f).IndEtale :=
  sorry

end RingHom.IndEtale
