/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.WLocalIndEtale.Over
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 61.8.7. A ring map inducing algebraic residue-field extensions admits
the canonical commutative square with all nine asserted properties. -/
@[stacks 097X] #check (Algebra.WLocalIndEtale.square_spec :
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Fact (Algebra.IsAlgebraicOnResidueFields A B)],
    (Algebra.WLocalIndEtale.toOver A B).comp
        (algebraMap A (Algebra.WLocalIndEtale.Cover A)) =
        (algebraMap B (Algebra.WLocalIndEtale.Over A B)).comp (algebraMap A B) ∧
      (algebraMap A (Algebra.WLocalIndEtale.Cover A)).FaithfullyFlat ∧
      (algebraMap A (Algebra.WLocalIndEtale.Cover A)).IndEtale ∧
      (algebraMap B (Algebra.WLocalIndEtale.Over A B)).FaithfullyFlat ∧
      (algebraMap B (Algebra.WLocalIndEtale.Over A B)).IndEtale ∧
      WLocalSpace (PrimeSpectrum (Algebra.WLocalIndEtale.Cover A)) ∧
      WLocalSpace (PrimeSpectrum (Algebra.WLocalIndEtale.Over A B)) ∧
      IsWLocalMap (PrimeSpectrum.comap (Algebra.WLocalIndEtale.toOver A B)) ∧
      PrimeSpectrum.comap (Algebra.WLocalIndEtale.toOver A B) ⁻¹'
          closedPoints (PrimeSpectrum (Algebra.WLocalIndEtale.Cover A)) =
        closedPoints (PrimeSpectrum (Algebra.WLocalIndEtale.Over A B)) ∧
      Set.SurjOn (PrimeSpectrum.comap (algebraMap A (Algebra.WLocalIndEtale.Cover A)))
        (closedPoints (PrimeSpectrum (Algebra.WLocalIndEtale.Cover A))) Set.univ ∧
      Set.SurjOn (PrimeSpectrum.comap (algebraMap B (Algebra.WLocalIndEtale.Over A B)))
        (closedPoints (PrimeSpectrum (Algebra.WLocalIndEtale.Over A B))) Set.univ ∧
      ∀ (m : Ideal (Algebra.WLocalIndEtale.Cover A)) [m.IsMaximal],
        StrictHenselianLocalRing (Localization.AtPrime m))
