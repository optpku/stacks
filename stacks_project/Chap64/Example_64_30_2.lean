/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap64.Example_64_30_2_Abstract
public import stacks_project.Chap64.Example_64_30_2_Tame

/-!
# Example 64.30.2 — Stacks tag 03VQ

The first clause uses the full continuous trace formula for every finite
coefficient ring, including noncommutative rings. The integer representative
is explicitly q minus the number of degree-one points.

Local source erratum: the printed unconditional strict bound omits the empty
family case. The corrected bound is -q < a ≤ q; |a| < q holds exactly when
the degree-one family is nonempty. Equality a=q is equivalent to every
positive-degree family being empty. The uploaded original text is unchanged.

The second clause constructs the actual tame multiplicative-group degree
extension and uses its actual closed points. Compatible Frobenius labels,
the kernel identification, and the full trace formula are conclusions about
those data; they are not additional assumptions. The same point families
satisfy both displayed counts, and geometric Frobenius acts by p inverse.
-/

@[expose] public section
open ProfiniteGrp
open ProfiniteGrp.ContinuousTrace

section Abstract

variable (extension : DegreeExtension.{0}) (q : ℕ) (hq : 1 ≤ q)
variable {ι : ℕ+ → Type} [∀ d, Fintype (ι d)]
variable (F : ∀ d, ι d → ConjClasses extension.middle)
variable (degree_class : ∀ d x, extension.degClass (F d x) = hatZNatCast d.val)
variable (traceFormula : ContinuousTrace.IsAbstractTraceFormula extension
  (ContinuousTrace.AbstractTraceData.ofFiniteSets q hq F degree_class))
variable (kernelEquiv : extension.G ≃ₜ* Multiplicative (PadicInt.PrimeTo q))
variable (unit : (PadicInt.PrimeTo q)ˣ) (frobenius : extension.middle)
variable (degree_frobenius : extension.deg frobenius = hatZOne)
variable (conjugation : ∀ x : extension.G,
  kernelEquiv (extension.conjHom frobenius x) =
    Multiplicative.ofAdd (unit.val * (kernelEquiv x).toAdd))

-- Example 64.30.2, abstract clause with the explicit local boundary correction.
#check (PadicInt.PrimeTo.exists_int_of_full_continuous_trace_formula
  extension q hq F degree_class traceFormula kernelEquiv unit frobenius
  degree_frobenius conjugation :
  ∃ a : ℤ, -(q : ℤ) < a ∧ a ≤ q ∧
    (q : PadicInt.PrimeTo q) * unit.val = (a : PadicInt.PrimeTo q) ∧
    (a.natAbs < q ↔ Nonempty (ι 1)) ∧
    (a = q ↔ ∀ d : ℕ+, IsEmpty (ι d)))

end Abstract

section Geometric

open MultiplicativeGroupTame
variable (p : ℕ) [Fact p.Prime]

-- Example 64.30.2, the actual tame geometric realization of the case a=1.
#check (tame_multiplicative_realization (p := p) :
  ∃ F : ∀ d : ℕ+, sourcePoints p d → ConjClasses (sourceExtension p).middle,
    ∃ hdeg : ∀ (d : ℕ+) (x : sourcePoints p d),
        (sourceExtension p).degClass (F d x) = hatZNatCast d.val,
      LabelsMatchOrbit p F ∧
      IsAbstractTraceFormula (sourceExtension p) (sourceTraceData p F hdeg) ∧
      (∃ (e : (sourceExtension p).G ≃ₜ* Multiplicative (PadicInt.PrimeTo p))
          (geometricFrobenius : (sourceExtension p).middle),
        (sourceExtension p).deg geometricFrobenius = hatZOne ∧
        ∀ x : (sourceExtension p).G,
          e ((sourceExtension p).conjHom geometricFrobenius x) =
            Multiplicative.ofAdd ((PadicInt.PrimeTo.natCastUnit p)⁻¹.val * (e x).toAdd)) ∧
      (p : PadicInt.PrimeTo p) * (PadicInt.PrimeTo.natCastUnit p)⁻¹.val = 1 ∧
      Nat.card (sourcePoints p 1) = p - 1 ∧
      Nat.card (sourcePoints p 2) = ((p ^ 2 - 1) - (p - 1)) / 2)

end Geometric
