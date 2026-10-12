/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.IndEtale.Basic
public import ReasLib.RingTheory.RingHom.IndZariski
public import ReasLib.RingTheory.RingHom.Local.Properties

@[expose] public section

universe u

namespace RingHom

/-- There are commutative rings and a ring homomorphism that identifies local
rings but is neither ind-étale nor ind-Zariski. -/
theorem exists_isIsoOnLocalRings_not_indEtale :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (f : A →+* B),
      f.IsIsoOnLocalRings ∧ ¬ f.IndEtale ∧ ¬ f.IndZariski := sorry

end RingHom
