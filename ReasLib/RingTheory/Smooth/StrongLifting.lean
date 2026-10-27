/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import ReasLib.RingTheory.RingHom.QuotientLift.LocallyNilpotent

@[expose] public section

universe u

namespace Algebra

/-- An algebra has strong lifting if every map into a quotient by a locally nilpotent ideal lifts through the quotient map. -/
class HasStrongLifting (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  exists_lift : ∀ {B : Type u} [CommRing B] [Algebra R B] (I : Ideal B),
    I.IsLocallyNilpotent → ∀ (f : S →ₐ[R] B ⧸ I),
      ∃ f' : S →ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp f' = f

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Smooth algebras lift maps through quotients by locally nilpotent ideals. -/
instance HasStrongLifting.ofSmooth [Smooth R S] : HasStrongLifting R S where
  exists_lift I hI f := Smooth.exists_lift_of_quotient_by_isLocallyNilpotent I hI f

/-- The strong lifting property supplies a lift of any map across a locally
nilpotent quotient. -/
theorem HasStrongLifting.exists_lift_comp [HasStrongLifting R S]
    {B : Type u} [CommRing B] [Algebra R B]
    (I : Ideal B) (hI : I.IsLocallyNilpotent) (f : S →ₐ[R] B ⧸ I) :
    ∃ f' : S →ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp f' = f :=
  sorry

/-- An `R`-algebra has the strong lifting property if and only if every map into
a locally nilpotent quotient lifts through the quotient map. -/
theorem HasStrongLifting.spec (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    HasStrongLifting R S ↔
      ∀ {B : Type u} [CommRing B] [Algebra R B] (I : Ideal B),
        I.IsLocallyNilpotent → ∀ (f : S →ₐ[R] B ⧸ I),
          ∃ f' : S →ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp f' = f :=
  sorry

end Algebra

end
