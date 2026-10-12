/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import StacksCheckRecall

/-! @stack 00UW -/

@[expose] public section

universe u v

namespace Algebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [EssFiniteType R S]
variable (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
variable [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
variable [Localization.AtPrime.IsLiesOverAlgebra p q]
variable [IsUnramifiedAt R q]

/- Lemma 10.151.5 (1): at an unramified prime, the extension of the
contracted prime is the maximal ideal after localization. -/
@[stacks 00UW "(1)"]
#check (((isUnramifiedAt_iff_map_eq R p q).mp
    (inferInstance : IsUnramifiedAt R q)).2 :
  p.map (algebraMap R (Localization.AtPrime q)) =
    IsLocalRing.maximalIdeal (Localization.AtPrime q))

/- Lemma 10.151.5 (2): the induced residue-field extension is finite and
separable. -/
@[stacks 00UW "(2)"]
#check (⟨inferInstance, inferInstance⟩ :
  FiniteDimensional p.ResidueField q.ResidueField ∧
    Algebra.IsSeparable p.ResidueField q.ResidueField)

#check (isUnramifiedAt_iff_map_eq R p q :
  IsUnramifiedAt R q ↔
    Algebra.IsSeparable p.ResidueField q.ResidueField ∧
      p.map (algebraMap R (Localization.AtPrime q)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime q))

end Algebra
