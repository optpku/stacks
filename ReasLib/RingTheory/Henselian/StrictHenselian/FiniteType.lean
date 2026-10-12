/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.Criteria
public import ReasLib.RingTheory.Henselian.Finite
public import ReasLib.RingTheory.Henselian.StrictHenselian
public import ReasLib.RingTheory.LocalRing.Finite
public import ReasLib.RingTheory.LocalRing.ResidueField.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-type algebras over strictly henselian local rings

This leaf refines the henselian finite-part decomposition by recording the
purely inseparable residue extensions forced by a strictly henselian base.

@stack 06DD
-/

@[expose] public section

open IsLocalRing

universe u v

namespace StrictHenselianLocalRing.FiniteType

/-- Lemma 10.153.6: a finite-type algebra over a strictly henselian local ring
has a finite-product part whose factor residue extensions are finite purely
inseparable, together with a remainder having no quasi-finite closed-fiber
point. -/
@[stacks 06DD "strictly henselian finite-type decomposition"]
theorem existsFinitePartDecomposition
    {R : Type u} {S : Type v} [CommRing R] [StrictHenselianLocalRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] :
    ∃ D : Algebra.FinitePartDecomposition R S,
      ∃ E : HenselianLocalRing.FiniteProduct R D.finitePart,
        (∀ i : E.index,
          RingHom.ResidueField.FinitePurelyInseparable
            (algebraMap R (E.factor i))
            (Algebra.isLocalHom_of_moduleFinite (R := R) (S := E.factor i))) ∧
          D.noQuasiFinitePoints (closedPoint R) := sorry

end StrictHenselianLocalRing.FiniteType
