/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.AtPrime

@[expose] public section

/-!
# Relative scalar actions on completed prime local rings

For an algebra map `R → S` and a prime `q` of `S`, this leaf owns the
explicit algebra action of the completed local ring at `q.under R` on the
completed local ring at `q`.  It is not a global instance because it depends
on the chosen prime-local map.
-/

open IsLocalRing

universe u v

namespace AdicCompletion.AtPrime.Relative

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- Tag `07NC`: the completion-algebra structure induced by the canonical map from
`R_(q.under R)` to `S_q`. -/
@[stacks 07NC "relative completed local algebra"]
noncomputable abbrev mapAlgebra (q : Ideal S) [q.IsPrime] :
    Algebra
      (AdicCompletion (maximalIdeal (Localization.AtPrime (q.under R)))
        (Localization.AtPrime (q.under R)))
      (AdicCompletion (maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q)) :=
  AdicCompletion.mapLocalAlgebra
    (Localization.localRingHom (q.under R) q (algebraMap R S) rfl)

/-- Tag `07NC`: the algebra map of `mapAlgebra` is the canonical map between the corresponding
completed local rings. -/
@[stacks 07NC "relative completed local algebra"]
theorem algebraMap_eq_mapLocal (q : Ideal S) [q.IsPrime] :
    letI : Algebra
        (AdicCompletion (maximalIdeal (Localization.AtPrime (q.under R)))
          (Localization.AtPrime (q.under R)))
        (AdicCompletion (maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q)) :=
      mapAlgebra q
    algebraMap
        (AdicCompletion (maximalIdeal (Localization.AtPrime (q.under R)))
          (Localization.AtPrime (q.under R)))
        (AdicCompletion (maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q)) =
      AdicCompletion.mapLocal
        (Localization.localRingHom (q.under R) q (algebraMap R S) rfl) := sorry

/-- Tag `07NC`: the explicit completed-local algebra action extends the original `R`-action. -/
@[stacks 07NC "relative completed local algebra"]
theorem mapAlgebra_isScalarTower (q : Ideal S) [q.IsPrime] :
    letI : Algebra
        (AdicCompletion (maximalIdeal (Localization.AtPrime (q.under R)))
          (Localization.AtPrime (q.under R)))
        (AdicCompletion (maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q)) :=
      mapAlgebra q
    IsScalarTower R
      (AdicCompletion (maximalIdeal (Localization.AtPrime (q.under R)))
        (Localization.AtPrime (q.under R)))
      (AdicCompletion (maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q)) := sorry

end AdicCompletion.AtPrime.Relative
