/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.SeparableClosure
public import ReasLib.RingTheory.LocalRing.ResidueField.Map

@[expose] public section

/-!
# Separable closures in residue-field extensions

This file records finiteness of the maximal separable subextension associated
to a pair of prime ideals related by lying over.
-/

universe u v

namespace Ideal.ResidueField

/-- The maximal separable subextension of the residue extension at a
lying-over pair is finite over the base residue field. -/
def FiniteSeparablePart
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] : Prop :=
  -- Local instance justification (noncanonical choice): this algebra depends on the selected lying-over pair and must not be global.
  letI : Algebra p.ResidueField q.ResidueField := algebraOfLiesOver p q
  Module.Finite p.ResidueField (separableClosure p.ResidueField q.ResidueField)

/-- `FiniteSeparablePart` is the finiteness of the canonical maximal separable
subextension for the selected lying-over residue-field algebra. -/
theorem finiteSeparablePart_iff
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    FiniteSeparablePart p q ↔
      -- Local instance justification (noncanonical choice): this algebra depends on the selected lying-over pair and is scoped to this specification.
      letI : Algebra p.ResidueField q.ResidueField := algebraOfLiesOver p q
      Module.Finite p.ResidueField
        (separableClosure p.ResidueField q.ResidueField) := sorry

end Ideal.ResidueField
