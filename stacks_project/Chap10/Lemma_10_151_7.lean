module

public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import StacksCheckRecall

/-! @stack 02FM -/

@[expose] public section

universe u v

namespace Algebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [FiniteType R S]
variable (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
variable [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
variable [Localization.AtPrime.IsLiesOverAlgebra p q]

/- Lemma 10.151.7: a finite-type map is unramified at `q` when the extended
contracted prime is maximal and the residue-field extension is separable. The
canonical criterion absorbs the source's redundant finite-dimensionality
hypothesis. -/
@[stacks 02FM]
#check (isUnramifiedAt_iff_map_eq R p q :
  IsUnramifiedAt R q ↔
    Algebra.IsSeparable p.ResidueField q.ResidueField ∧
      p.map (algebraMap R (Localization.AtPrime q)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime q))

end Algebra
