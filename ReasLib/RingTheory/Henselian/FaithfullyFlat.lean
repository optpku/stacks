/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import ReasLib.RingTheory.Henselian.Flat
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Faithful flatness of Henselizations

The structural maps of Henselizations and strict Henselizations are flat local maps, hence
faithfully flat. These canonical facts are instances so downstream code does not need local
`letI` declarations to recover module flatness.

@stack 04GN
@stack 04GP
-/

@[expose] public section

universe u v

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

namespace IsHenselizationOf

/-- A Henselization is faithfully flat as a module over its base ring. -/
@[stacks 04GN "faithful flatness of a Henselization"]
instance moduleFaithfullyFlat [IsHenselizationOf R S] : Module.FaithfullyFlat R S := sorry

/-- The structural ring map of a Henselization is faithfully flat. -/
@[stacks 04GN "faithfully flat Henselization map"]
theorem faithfullyFlat [IsHenselizationOf R S] :
    (algebraMap R S).FaithfullyFlat := sorry

/-- The structural ring map of a Henselization is injective. -/
@[stacks 04GN "injectivity of a Henselization map"]
theorem injective [IsHenselizationOf R S] :
    Function.Injective (algebraMap R S) :=
  RingHom.FaithfullyFlat.injective (faithfullyFlat (R := R) (S := S))

end IsHenselizationOf

namespace IsStrictHenselizationOf

/-- A strict Henselization is faithfully flat as a module over its base ring. -/
@[stacks 04GP "faithful flatness of a strict Henselization"]
instance moduleFaithfullyFlat [IsStrictHenselizationOf R S] :
    Module.FaithfullyFlat R S := sorry

/-- The structural ring map of a strict Henselization is faithfully flat. -/
@[stacks 04GP "faithfully flat strict Henselization map"]
theorem faithfullyFlat [IsStrictHenselizationOf R S] :
    (algebraMap R S).FaithfullyFlat := sorry

end IsStrictHenselizationOf

end
