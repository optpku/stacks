/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.AtPrime
public import ReasLib.RingTheory.RingHom.Unramified

@[expose] public section

/-!
# G-Unramified Algebras

Mathlib's `Algebra.Unramified` models an unramified finite-type algebra.
This leaf adds the reusable finite-presentation refinement used by the Stacks
Project, together with its basic-open primewise formulations. The canonical
pointwise owner remains Mathlib's `Algebra.IsUnramifiedAt`.

@stack 00UT
@stack 00UU
-/

universe u v

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- Unramifiedness is equivalently formal unramifiedness together with finite type. -/
@[stacks 00UU "unramifiedness as formally unramified finite type"]
theorem Unramified.iff_formallyUnramified_and_finiteType :
    Unramified R S ↔ FormallyUnramified R S ∧ FiniteType R S := sorry

/-- An `R`-algebra is G-unramified when it is unramified and finitely presented over `R`. -/
@[stacks 00UT]
class GUnramified : Prop extends Unramified R S, FinitePresentation R S

namespace GUnramified

/-- A formally unramified finitely presented algebra is G-unramified. -/
@[stacks 00UT "formally unramified finite presentations are G-unramified"]
instance instOfFormalFp
    [FormallyUnramified R S] [FinitePresentation R S] : Algebra.GUnramified R S where
  toUnramified := {}
  toFinitePresentation := inferInstance

/-- G-unramifiedness is equivalently unramifiedness together with finite presentation. -/
@[stacks 00UT "G-unramifiedness as unramified finite presentation"]
theorem iff_unramified_and_finitePresentation :
    GUnramified R S ↔ Unramified R S ∧ FinitePresentation R S := sorry

/-- G-unramifiedness is equivalently formal unramifiedness together with finite presentation. -/
@[stacks 00UU "G-unramifiedness as formally unramified finite presentation"]
theorem iff_formallyUnramified_and_finitePresentation :
    GUnramified R S ↔ FormallyUnramified R S ∧ FinitePresentation R S := sorry

end GUnramified

end Algebra

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring homomorphism is G-unramified when its induced algebra is
unramified and finitely presented. -/
@[stacks 00UT "G-unramified ring homomorphism", algebraize RingHom.GUnramified.toAlgebra]
def GUnramified (f : R →+* S) : Prop :=
  @Algebra.GUnramified R S _ _ f.toAlgebra

namespace GUnramified

/-- The intrinsic ring-hom predicate recovers G-unramifiedness for the
algebra structure induced by the map. -/
theorem toAlgebra {f : R →+* S} (hf : f.GUnramified) :
    @Algebra.GUnramified R S _ _ f.toAlgebra := sorry

end GUnramified

/-- The intrinsic ring-hom predicate on an algebra map is equivalent to the
ambient algebra-level G-unramified predicate. -/
@[stacks 00UT "G-unramified algebra maps"]
theorem gUnramified_algebraMap [Algebra R S] :
    (algebraMap R S).GUnramified ↔ Algebra.GUnramified R S := sorry

end RingHom

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- An `R`-algebra is unramified at `q` when it is unramified on a principal open
neighborhood of `q`. -/
@[stacks 00UT]
def UnramifiedAt (q : PrimeSpectrum S) : Prop :=
  RingHom.AtPrime (fun f ↦ f.Unramified) (algebraMap R S) q

/-- An `R`-algebra is G-unramified at `q` when it is G-unramified on a principal open
neighborhood of `q`. -/
@[stacks 00UT]
def GUnramifiedAt (q : PrimeSpectrum S) : Prop :=
  RingHom.AtPrime (fun f ↦ f.GUnramified) (algebraMap R S) q

namespace UnramifiedAt

/-- `UnramifiedAt R S q` holds exactly when `S` is unramified over `R` on some
principal open neighborhood of `q`. -/
@[stacks 00UT "unramified on a principal-open neighborhood of a prime"]
theorem iff_exists_away (q : PrimeSpectrum S) :
    Algebra.UnramifiedAt R S q ↔
      ∃ g : S, g ∉ q.asIdeal ∧ Unramified R (Localization.Away g) := sorry

/-- For a finite-type algebra, the basic-open unramified-at condition is equivalent to
Mathlib's canonical pointwise predicate. -/
@[stacks 00UT "unramified basic-open and pointwise criteria"]
theorem iff_isUnramifiedAt [FiniteType R S] (q : PrimeSpectrum S) :
    Algebra.UnramifiedAt R S q ↔ IsUnramifiedAt R q.asIdeal := sorry

end UnramifiedAt

namespace GUnramifiedAt

/-- `GUnramifiedAt R S q` holds exactly when `S` is G-unramified over `R` on some
principal open neighborhood of `q`. -/
@[stacks 00UT "G-unramified on a principal-open neighborhood of a prime"]
theorem iff_exists_away (q : PrimeSpectrum S) :
    Algebra.GUnramifiedAt R S q ↔
      ∃ g : S, g ∉ q.asIdeal ∧ GUnramified R (Localization.Away g) := sorry

/-- For a finitely presented algebra, the basic-open G-unramified-at condition is equivalent to
Mathlib's canonical pointwise unramified predicate. -/
@[stacks 00UT "G-unramified basic-open and pointwise criteria"]
theorem iff_isUnramifiedAt [FinitePresentation R S] (q : PrimeSpectrum S) :
    Algebra.GUnramifiedAt R S q ↔ IsUnramifiedAt R q.asIdeal := sorry

end GUnramifiedAt

end Algebra
