/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Span
public import ReasLib.RingTheory.Etale.WContractible
public import ReasLib.RingTheory.Localization.Specializing

@[expose] public section

universe u

namespace IsWContractibleRing

/-- A w-contractible ring has w-contractible specializing localization at a
finitely generated ideal. -/
theorem specializing_of_fg {A : Type u} [CommRing A] [IsWContractibleRing A]
    {I : Ideal A} (hI : I.FG) :
    IsWContractibleRing (Localization.specializing (1 : A) I) :=
  sorry

/-- A finite family of elements defines a w-contractible specializing
localization of a w-contractible ring. -/
@[stacks 0987, instance]
instance specializing {A : Type u} [CommRing A] [IsWContractibleRing A]
    (s : Finset A) :
    IsWContractibleRing
      (Localization.specializing (1 : A) (Ideal.span (s : Set A))) :=
  sorry

end IsWContractibleRing
