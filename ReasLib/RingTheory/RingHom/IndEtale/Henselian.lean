/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Henselian
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.Fiber.ResidueLift
public import ReasLib.RingTheory.RingHom.IndEtale.Colimit

/-!
# Ind-etale lifting to henselian local rings

This file owns the residue-point lifting property of ind-etale algebras over
henselian local rings. The public statement uses `RingHom.IndEtale`; filtered
presentations and their universe bookkeeping remain implementation details.

@stack 08HR
-/

@[expose] public section

open IsLocalRing

universe u v w x

namespace RingHom.IndEtale

variable {R : Type u} {A : Type v} {S : Type w}
variable [CommRing R] [CommRing A] [CommRing S]
variable [Algebra R A] [Algebra R S] [HenselianLocalRing S]

/-- A compatible residue-field point of an ind-etale algebra has a unique lift
to a henselian local algebra. -/
@[stacks 08HR]
theorem existsUnique_lift
    (hA : (algebraMap R A).IndEtale)
    (q : PrimeSpectrum A)
    (hq : q.asIdeal.under R = (maximalIdeal S).under R)
    (τ : q.asIdeal.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map
        (q.asIdeal.under R) q.asIdeal (algebraMap R A) rfl) =
      Ideal.ResidueField.map
        (q.asIdeal.under R) (maximalIdeal S) (algebraMap R S) hq) :
    ∃! f : A →ₐ[R] S,
      f.IsResidueLift q (closedPoint S) τ := sorry

/-- The residue-point lifting theorem also accepts an arbitrary-universe
ind-etale presentation, so consumers do not need to normalize a filtered
presentation before invoking the lifting API. -/
@[stacks 08HR "ind-etale residue-point lift from a raw presentation"]
theorem existsUnique_lift_ofRaw
    (hA : RingHom.IndEtale.Raw.{u, v, x} (algebraMap R A))
    (q : PrimeSpectrum A)
    (hq : q.asIdeal.under R = (maximalIdeal S).under R)
    (τ : q.asIdeal.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map
        (q.asIdeal.under R) q.asIdeal (algebraMap R A) rfl) =
      Ideal.ResidueField.map
        (q.asIdeal.under R) (maximalIdeal S) (algebraMap R S) hq) :
    ∃! f : A →ₐ[R] S,
      f.IsResidueLift q (closedPoint S) τ := sorry

end RingHom.IndEtale
