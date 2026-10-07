module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.MultiplicativeGroup
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import stacks_project.Chap64.Example_64_30_2_PrimeTo
public import stacks_project.Chap64.Remark_64_30_1_Formula

/-!
# Example 64.30.2

Rigidity of `q * u` for a profinite degree extension with kernel
`PadicInt.PrimeTo q` and an abstract trace formula. Arithmetic and closed-point
count companions for the multiplicative-group example are retained below.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry ProfiniteGrp
open scoped AlgebraicGeometry Topology

namespace PadicInt.PrimeTo

/-- Example 64.30.2 (1): an abstract trace-formula extension whose degree-
indexed conjugacy-class data are given by finite families forces the strict
integer bound. The kernel is identified as a topological group with the
product of prime-to-`q` adic integers, and a degree-one lift acts by
multiplication by `unit`. Reversing the conjugation convention gives the same
statement with `unit⁻¹`. -/
@[stacks 03VQ]
theorem exists_int_of_congruence
    (extension : DegreeExtension.{0})
    (q : ℕ) (hq : 1 ≤ q)
    {ι : ℕ+ → Type} [∀ d, Fintype (ι d)]
    (F : ∀ d, ι d → ConjClasses extension.middle)
    (degree_class : ∀ d x,
      extension.degClass (F d x) = hatZNatCast d.val)
    (traceFormula :
      IsAbstractTraceFormula extension
        (AbstractTraceData.ofFiniteSets q hq F degree_class))
    (kernelEquiv : extension.G ≃ₜ* Multiplicative (PrimeTo q))
    (unit : (PrimeTo q)ˣ) (frobenius : extension.middle)
    (degree_frobenius : extension.deg frobenius = hatZOne)
    (conjugation : ∀ x : extension.G,
      kernelEquiv (extension.conjHom frobenius x) =
        Multiplicative.ofAdd (unit.val * (kernelEquiv x).toAdd))
    : ∃ a : ℤ, Int.natAbs a < q ∧
      (q : PrimeTo q) * unit.val = (a : PrimeTo q) := sorry

/-! Arithmetic companion for the source's special case `a = 1`. -/
@[stacks 03VQ]
theorem mul_natCastUnit_inv (p : ℕ) [Fact p.Prime] [NeZero p] :
    (p : PrimeTo p) * (natCastUnit p)⁻¹.val = 1 := sorry

end PadicInt.PrimeTo

namespace AlgebraicGeometry.SchemeOverField

/-- The multiplicative group scheme over the prime field `ZMod p`. -/
abbrev gmOver (p : ℕ) [Fact p.Prime] : SchemeOverField (ZMod p) :=
  (𝔾ₘ[Spec (CommRingCat.of (ZMod p))]).X

/-! Closed-point count used by the degree-one part of the bridge. -/
@[stacks 03VQ]
theorem gm_closedPoint_card_one (p : ℕ) [Fact p.Prime] :
    Nat.card {x : closedPoints (gmOver p).left //
      (gmOver p).hom.residueDegree x.1 = 1} = p - 1 := sorry

/-! Closed-point count used by the degree-two part of the bridge. -/
@[stacks 03VQ]
theorem gm_closedPoint_card_two (p : ℕ) [Fact p.Prime] :
    Nat.card {x : closedPoints (gmOver p).left //
      (gmOver p).hom.residueDegree x.1 = 2} =
      ((p ^ 2 - 1) - (p - 1)) / 2 := sorry

end AlgebraicGeometry.SchemeOverField
