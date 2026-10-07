module

public import ReasLib.RingTheory.RingHom.Local.Properties
public import stacks_project.Chap61.Lemma_61_5_3_Ring
import Mathlib.Tactic.CrossRefAttribute

/-!
# Proposition 61.6.6

A ring map that identifies local rings admits a faithfully flat ind-Zariski
extension whose composite is ind-Zariski.
-/

@[expose] public section

universe u

open Algebra.WLocalHull

namespace RingHom.IndZariski

/-- If `f : A →+* B` identifies local rings, the composite of `f` with the
structure map of `wLocalization B` is ind-Zariski. -/
theorem wLocalization_comp {A B : Type u} [CommRing A] [CommRing B]
    {f : A →+* B} (hf : f.IsIsoOnLocalRings) :
    ((algebraMap B (wLocalization B)).comp f).IndZariski :=
  sorry

/-- Proposition 61.6.6: if `f : A →+* B` identifies local rings, then there
exists a faithfully flat, ind-Zariski ring map `g : B →+* B'` such that
`g.comp f` is ind-Zariski. -/
@[stacks 097G]
theorem exists_faithfullyFlat_of_isIsoOnLocalRings
    {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}
    (hf : f.IsIsoOnLocalRings) :
    ∃ (B' : Type u) (_ : CommRing B') (g : B →+* B'),
      g.FaithfullyFlat ∧ g.IndZariski ∧ (g.comp f).IndZariski :=
  sorry

end RingHom.IndZariski
