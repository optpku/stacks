module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.SquareZero

/-!
# Presentation relations over principal square-zero extensions

A relation in a polynomial presentation can be lifted coefficientwise across a principal
square-zero extension.  When the lifted sum is a chosen kernel generator times a factor, reducing
and evaluating that factor defines the presentation obstruction in the target modulo the
intrinsic kernel annihilator.

This is presentation-level infrastructure.  Consequences for Tor dimension and perfect maps live
in the corresponding application files.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

universe u' u v w t

namespace Algebra.Presentation

variable {R' : Type u'} {R : Type u} {S : Type v}
variable [CommRing R'] [CommRing R] [CommRing S] [Algebra R S]
variable {f : R' →+* R} [f.IsSquareZeroExtension]
variable {g : RingHom.SquareZeroExtension.Generator f}
variable {ι : Type w} {σ : Type t} [Fintype σ]

/-- A polynomial relation and compatible coefficientwise lifts across a principal square-zero
extension, together with its factor by the chosen kernel generator. -/
@[stacks 09PT "lifted presentation relation", stacks 09PU "lifted presentation relation"]
structure LiftedRelation (g : RingHom.SquareZeroExtension.Generator f)
    (P : Presentation R S ι σ) where
  /-- The coefficients of the relation among the displayed presentation relations. -/
  coefficient : σ → P.Ring
  /-- The displayed linear combination of relations vanishes. -/
  sum_eq_zero : ∑ j, coefficient j * P.relation j = 0
  /-- Chosen coefficientwise lifts to the source of the square-zero extension. -/
  liftedCoefficient : σ → MvPolynomial ι R'
  /-- Chosen lifts of the displayed presentation relations. -/
  liftedRelation : σ → MvPolynomial ι R'
  /-- The coefficient lifts reduce to the original coefficients. -/
  map_liftedCoefficient (j : σ) :
    MvPolynomial.map f (liftedCoefficient j) = coefficient j
  /-- The relation lifts reduce to the displayed presentation relations. -/
  map_liftedRelation (j : σ) :
    MvPolynomial.map f (liftedRelation j) = P.relation j
  /-- The factor left after dividing the lifted relation by the chosen kernel generator. -/
  factor : MvPolynomial ι R'
  /-- The lifted relation is the chosen kernel generator times `factor`. -/
  lifted_sum_eq :
    ∑ j, liftedCoefficient j * liftedRelation j =
      MvPolynomial.C g.element * factor
  /-- Every coefficient of the original relation lies in the intrinsic kernel annihilator. -/
  coefficient_mem_annihilator (j : σ) (d : ι →₀ ℕ) :
    MvPolynomial.coeff d (coefficient j) ∈
      RingHom.SquareZeroExtension.kernelAnnihilator f

namespace LiftedRelation

variable {P : Presentation R S ι σ}

/-- The coefficientwise annihilator condition places each presentation coefficient in the
extension of the intrinsic kernel annihilator to the polynomial presentation ring. -/
theorem coefficient_mem_annihilatorIdeal (L : LiftedRelation g P) (j : σ) :
    L.coefficient j ∈
      RingHom.SquareZeroExtension.kernelAnnihilatorIdeal f P.Ring := sorry

/-- The polynomial factor of the lifted relation, reduced coefficientwise to the intrinsic
kernel-annihilator quotient. -/
@[stacks 09PT "polynomial square-zero obstruction factor"]
def factorClass (L : LiftedRelation g P) :
    MvPolynomial ι (R ⧸ RingHom.SquareZeroExtension.kernelAnnihilator f) :=
  MvPolynomial.map
    (Ideal.Quotient.mk (RingHom.SquareZeroExtension.kernelAnnihilator f))
    (MvPolynomial.map f L.factor)

/-- The obstruction class in `S` modulo the extended annihilator ideal, obtained by reducing and
evaluating the factor of a lifted relation. -/
@[stacks 09PT "lifted relation obstruction class",
  stacks 09PU "lifted relation obstruction class"]
def obstruction (L : LiftedRelation g P) :
    RingHom.SquareZeroExtension.kernelAnnihilatorQuotient f S :=
  Ideal.Quotient.mk (RingHom.SquareZeroExtension.kernelAnnihilatorIdeal f S)
    (MvPolynomial.aeval P.val (MvPolynomial.map f L.factor))

/-- Evaluating `factorClass` in the quotient presentation algebra gives the obstruction class. -/
theorem obstruction_eq_aeval_factorClass (L : LiftedRelation g P) :
    L.obstruction =
      MvPolynomial.aeval
        (fun i ↦ Ideal.Quotient.mk
          (RingHom.SquareZeroExtension.kernelAnnihilatorIdeal f S) (P.val i))
        L.factorClass := sorry

end LiftedRelation

end Algebra.Presentation
