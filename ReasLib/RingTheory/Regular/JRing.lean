/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.Basic
public import ReasLib.RingTheory.Spectrum.Prime.RegularLocus
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# J-rings

@stack 07P7

The three `J` conditions are owner classes.  In particular, `IsJ2Ring` records Noetherianity and
does not register its finite-type projection as an instance: the target algebra does not determine
the hidden base ring.
-/

open PrimeSpectrum
open scoped PrimeSpectrum

universe u v

/-- A ring is `J-0` when it is Noetherian and its regular locus contains a nonempty open set. -/
@[stacks 07P7 "(1), J-0 rings"]
class IsJ0Ring (R : Type u) [CommRing R] : Prop extends IsNoetherianRing R where
  /-- A nonempty open subset contained in the regular locus. -/
  exists_nonempty_open_subset_regularLocus :
    ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ U.Nonempty ∧ U ⊆ Reg(Spec R)

/-- A Noetherian ring is `J-0` exactly when its regular locus contains a nonempty open set. -/
@[stacks 07P7 "J-0 characterization by an open regular subset"]
theorem isJ0Ring_iff_exists_nonempty_open_subset_regularLocus
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsJ0Ring R ↔
      ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ U.Nonempty ∧ U ⊆ Reg(Spec R) := sorry

namespace IsJ0Ring

/-- Every nontrivial regular ring is `J-0`. -/
@[stacks 07P7 "regular rings are J-0"]
theorem of_isRegularRing (R : Type u) [CommRing R] [Nontrivial R] [IsRegularRing R] :
    IsJ0Ring R := sorry

/-- In a `J-0` domain, some nonzero principal localization is regular. -/
@[stacks 07P7 "regular principal localization in a J-0 domain"]
theorem exists_regularLocalization
    (A : Type u) [CommRing A] [IsDomain A] [IsJ0Ring A] :
    ∃ a : A, a ≠ 0 ∧ IsRegularRing (Localization.Away a) := sorry

end IsJ0Ring

/-- A ring is `J-1` when it is Noetherian and its regular locus is open. -/
@[stacks 07P7 "(2), J-1 rings"]
class IsJ1Ring (R : Type u) [CommRing R] : Prop extends IsNoetherianRing R where
  /-- Openness of the regular locus. -/
  regularLocus_isOpen : IsOpen (Reg(Spec R))

/-- A Noetherian ring is `J-1` exactly when its regular locus is open. -/
@[stacks 07P7 "J-1 characterization by openness of the regular locus"]
theorem isJ1Ring_iff_regularLocus_isOpen
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsJ1Ring R ↔ IsOpen (Reg(Spec R)) := sorry

/-- A ring is `J-2` when it is Noetherian and every finite type algebra over it is `J-1`. -/
@[stacks 07P7 "(3), J-2 rings"]
class IsJ2Ring (R : Type u) [CommRing R] : Prop extends IsNoetherianRing R where
  /-- Every finite type algebra over the base ring is `J-1`. -/
  isJ1Ring_of_finiteType {A : Type v} [CommRing A] [Algebra R A]
      [Algebra.FiniteType R A] : IsJ1Ring A

/-- A Noetherian ring is `J-2` exactly when every finite type algebra over it is `J-1`. -/
@[stacks 07P7 "J-2 characterization by finite type algebras"]
theorem isJ2Ring_iff_forall_finiteType_isJ1
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    IsJ2Ring.{u, v} R ↔
      ∀ (A : Type v) [CommRing A] [Algebra R A] [Algebra.FiniteType R A], IsJ1Ring A := sorry
