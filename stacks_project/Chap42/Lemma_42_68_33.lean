module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant.UnitAction
import StacksCheckRecall

@[expose] public section

open scoped nonZeroDivisors

universe u v

/- Lemma 42.68.33 (1): if `u` is a unit and `b` is regular on a finite
dimension-one module `M`, then `d_M(u, b)` is the residue of `u` raised to the
length of `M ⧸ b • ⊤`. -/
@[stacks 02Q2] #check
  (CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientDeterminant_unit_left :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
      (u : Aˣ) (b : A) (hb : IsSMulRegular M b)
      (hdim : Module.supportDim A M = 1),
      CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientDeterminant
          M (u : A) b (u.isSMulRegular M) hb hdim =
        Units.map (IsLocalRing.residue A).toMonoidHom u ^
          (Module.length A (QuotSMulTop b M)).toNat)

/- Lemma 42.68.33 (2): for the self-module `A`, the exponent in the unit formula
for `d_A(u, b)` is the order of vanishing of `b`. -/
@[stacks 02Q2] #check
  (CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant_unit_left :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (u : Aˣ) (b : A) (hb : b ∈ A⁰) (hdim : ringKrullDim A = 1),
      CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
          (u : A) b u.isUnit.mem_nonZeroDivisors hb hdim =
        Units.map (IsLocalRing.residue A).toMonoidHom u ^ (Ring.ord A b).toNat)
