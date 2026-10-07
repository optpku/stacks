module

import ReasLib.RingTheory.QuasiFinite.TopologyFiniteType
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 110.39.1 -/
@[stacks 05JI]
#check (RingHom.exists_local_essFiniteType_residueFinite_not_localization_quasiFinite :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : IsLocalRing A) (_ : IsLocalRing B)
      (_ : IsDomain A) (_ : IsDomain B) (f : A →+* B) (_ : IsLocalHom f),
      f.EssFiniteType ∧
        (IsLocalRing.ResidueField.map f).Finite ∧
        ∀ (q : Ideal B), q.IsPrime → q ≠ IsLocalRing.maximalIdeal B →
          ¬ ((Ideal.Quotient.mk q).comp f).IsLocalizationOfQuasiFinite)
