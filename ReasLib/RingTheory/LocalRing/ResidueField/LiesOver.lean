/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.ResidueField.Map
public import ReasLib.RingTheory.LocalRing.ResidueField.MaximalIdeal

@[expose] public section

/-!
# Residue-field scalar towers for lying-over primes

For a prime `P` of an `R`-algebra `S` lying over `p`, the induced map
`κ(p) → κ(P)` determines a compatible `(R ⧸ p)`-algebra structure on
`κ(P)` and scalar towers comparing the quotient rings with the residue fields.

These structures are deliberately not global instances: different
lying-over pairs can put competing algebra structures on the same carrier.
-/

universe u v

namespace Ideal.ResidueField.LiesOver

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- The `(R ⧸ p)`-algebra structure on `κ(P)` obtained by composing through
the residue-field map `κ(p) → κ(P)`. -/
@[implicit_reducible, stacks 0BRJ "quotient algebra induced by a lying-over pair"]
noncomputable def quotientAlgebra
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    Algebra (R ⧸ p) P.ResidueField :=
  ((Ideal.ResidueField.map p P (algebraMap R S) (Ideal.over_def P p)).comp
    (algebraMap (R ⧸ p) p.ResidueField)).toAlgebra

/-- The algebra map of `quotientAlgebra` is the canonical composite
`R ⧸ p → κ(p) → κ(P)`. -/
@[stacks 0BRJ "algebra map of the quotient algebra for a lying-over pair"]
theorem quotientAlgebraMap_eq
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    -- Local instance justification (noncanonical choice): the quotient algebra is attached to
    -- the selected lying-over pair.
    letI : Algebra (R ⧸ p) P.ResidueField := quotientAlgebra p P
    algebraMap (R ⧸ p) P.ResidueField =
      (Ideal.ResidueField.map p P (algebraMap R S) (Ideal.over_def P p)).comp
        (algebraMap (R ⧸ p) p.ResidueField) := sorry

/-- The towers `(R ⧸ p) → κ(p) → κ(P)` and
`(R ⧸ p) → κ(P)` induced by a lying-over pair are compatible. -/
@[stacks 0BRJ "residue-field scalar tower for a lying-over pair"]
theorem isScalarTower_residue
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    -- Local instance justification (noncanonical choice): the residue algebra is attached to
    -- the selected lying-over pair.
    letI : Algebra p.ResidueField P.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p P
    -- Local instance justification (instance diamond): use the compatible quotient algebra for
    -- this same lying-over pair.
    letI : Algebra (R ⧸ p) P.ResidueField := quotientAlgebra p P
    IsScalarTower (R ⧸ p) p.ResidueField P.ResidueField := sorry

/-- The towers `(R ⧸ p) → (S ⧸ P) → κ(P)` and
`(R ⧸ p) → κ(P)` induced by a lying-over pair are compatible. -/
@[stacks 0BRJ "quotient scalar tower for a lying-over pair"]
theorem isScalarTower_quotient
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    -- Local instance justification (noncanonical choice): the quotient algebra is attached to
    -- the selected lying-over pair.
    letI : Algebra (R ⧸ p) P.ResidueField := quotientAlgebra p P
    IsScalarTower (R ⧸ p) (S ⧸ P) P.ResidueField := sorry

/-- Residue fields at a lying-over pair have the same characteristic. -/
@[stacks 09EE "residue characteristic along a lying-over pair"]
theorem ringChar_eq
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    ringChar p.ResidueField = ringChar P.ResidueField := sorry

/-- If `S ⧸ q` is finite over `R`, then the residue field at a maximal ideal
`q` lying over a maximal ideal `p` is finite over `κ(p)`.  The residue-field
algebra is scoped because it depends on the chosen lying-over pair. -/
@[stacks 0BRJ "residue-field finiteness from a finite quotient"]
theorem moduleFinite_of_quotient
    {p : Ideal R} [p.IsMaximal] {q : Ideal S} [q.IsMaximal] [q.LiesOver p]
    (hfin : Module.Finite R (S ⧸ q)) :
    -- Local instance justification (noncanonical choice): the residue-field algebra depends on
    -- the selected lying-over maximal ideal.
    letI : Algebra p.ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q
    Module.Finite p.ResidueField q.ResidueField := sorry

/-- A prime lying over a maximal ideal is maximal when the induced residue-field extension is
algebraic.  The algebra structure is scoped to the chosen lying-over pair. -/
@[stacks 00GA "maximality from an algebraic residue-field extension"]
theorem isMaximal_of_isAlgebraic
    {p : Ideal R} [p.IsMaximal] {P : Ideal S} [P.IsPrime] [P.LiesOver p]
    [let _ : Algebra p.ResidueField P.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p P
     Algebra.IsAlgebraic p.ResidueField P.ResidueField] :
    P.IsMaximal := sorry

end Ideal.ResidueField.LiesOver
