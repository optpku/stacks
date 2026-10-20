/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ChainGradedAlgebra.Quotient
public import ReasLib.RingTheory.RingHom.SquareZero.Module

/-!
# Dividing graded derivations over principal square-zero extensions

If the values of a homogeneous derivation are multiples of a chosen generator of a square-zero
kernel, division by that generator takes values in the quotient by its annihilator.  Under the
explicit descent and Leibniz conditions, these component maps assemble to a derivation on the
degreewise quotient graded algebra.
-/

@[expose] public section

noncomputable section

universe u v w

open RingHom.SquareZeroExtension

namespace ChainGradedAlgebra

namespace Derivation

variable {R' : Type u} {R : Type v} [CommRing R'] [CommRing R]
variable {f : R' →+* R} [f.IsSquareZeroExtension]
variable {A : ChainGradedAlgebra.{u, w} R'} {k : ℤ}

/-- Divide the values of a homogeneous derivation by a principal square-zero kernel generator,
before descending the source modulo the generator annihilator. -/
@[stacks 09PS "componentwise division of a graded derivation"]
def divideMap (g : Generator f) (D : Derivation A k)
    (h_exact : ∀ i, g.IsExactOn (A.X i))
    (h_range : ∀ i x, D i x ∈ LinearMap.range (g.moduleMul (A.X (i + k))))
    (i : ℤ) :
    A.X i →ₗ[R'] sourceKernelQuotientModule f (A.X (i + k)) :=
  g.divide (A.X (i + k)) (h_exact (i + k))
    (toHomogeneousMap D i) (h_range i)

/-- Multiplication by the chosen generator recovers a derivation from its componentwise
division. -/
@[simp]
theorem quotientEquivRange_divideMap (g : Generator f) (D : Derivation A k)
    (h_exact : ∀ i, g.IsExactOn (A.X i))
    (h_range : ∀ i x, D i x ∈ LinearMap.range (g.moduleMul (A.X (i + k))))
    (i : ℤ) (x : A.X i) :
    (((g.quotientEquivRange (A.X (i + k)) (h_exact (i + k)))
        (divideMap g D h_exact h_range i x) :
          LinearMap.range (g.moduleMul (A.X (i + k)))) : A.X (i + k)) =
      D i x := sorry

/-- Descend componentwise division to a linear map between homogeneous annihilator quotients. -/
@[stacks 09PS "quotient component of a divided graded derivation"]
def divideQuotientMap (g : Generator f) (D : Derivation A k)
    (h_exact : ∀ i, g.IsExactOn (A.X i))
    (h_range : ∀ i x, D i x ∈ LinearMap.range (g.moduleMul (A.X (i + k))))
    (h_kills : ∀ i, sourceKernelAnnihilator f • (⊤ : Submodule R' (A.X i)) ≤
      LinearMap.ker (divideMap g D h_exact h_range i))
    (i : ℤ) :
    IdealQuotient.Piece A (sourceKernelAnnihilator f) i →ₗ[R' ⧸ sourceKernelAnnihilator f]
      IdealQuotient.Piece A (sourceKernelAnnihilator f) (i + k) :=
  LinearMap.IdealQuotient.descend (sourceKernelAnnihilator f)
    (divideMap g D h_exact h_range i) (h_kills i)

/-- A graded derivation is divisible by a chosen principal square-zero kernel generator when the
canonical componentwise divisions descend and satisfy the quotient graded Leibniz rule. -/
@[stacks 09PS "divisibility of a graded derivation by a square-zero kernel generator"]
structure IsDivisibleBy (D : Derivation A k) (g : Generator f) : Prop where
  /-- Multiplication by the generator has the expected kernel on every homogeneous component. -/
  exact : ∀ i, g.IsExactOn (A.X i)
  /-- Every value of the derivation is a multiple of the generator. -/
  range : ∀ i x, D i x ∈ LinearMap.range (g.moduleMul (A.X (i + k)))
  /-- Componentwise division kills the annihilator multiples in its source. -/
  kills : ∀ i, sourceKernelAnnihilator f • (⊤ : Submodule R' (A.X i)) ≤
    LinearMap.ker (divideMap g D exact range i)
  /-- The descended component maps satisfy the graded Leibniz rule. -/
  leibniz : SatisfiesLeibniz
    (A.quotientByIdeal (sourceKernelAnnihilator f)) k
    (divideQuotientMap g D exact range kills)

namespace IsDivisibleBy

variable {D : Derivation A k} {g : Generator f}

/-- Division by a principal square-zero kernel generator, as a derivation on the homogeneous
annihilator quotient. -/
@[stacks 09PS "divided derivation on the annihilator quotient"]
def divide (h : IsDivisibleBy D g) :
    Derivation (A.quotientByIdeal (sourceKernelAnnihilator f)) k :=
  ⟨divideQuotientMap g D h.exact h.range h.kills, h.leibniz⟩

/-- The divided derivation sends the quotient class of a homogeneous representative to its
componentwise divided value. -/
@[simp]
theorem divide_mk (h : IsDivisibleBy D g) (i : ℤ) (x : A.X i) :
    h.divide i (IdealQuotient.mk A (sourceKernelAnnihilator f) i x) =
      divideMap g D h.exact h.range i x := sorry

/-- Multiplication by the generator recovers the original derivation on every homogeneous
representative. -/
@[simp]
theorem quotientEquivRange_divide_mk (h : IsDivisibleBy D g) (i : ℤ) (x : A.X i) :
    (((g.quotientEquivRange (A.X (i + k)) (h.exact (i + k)))
        (h.divide i (IdealQuotient.mk A (sourceKernelAnnihilator f) i x)) :
          LinearMap.range (g.moduleMul (A.X (i + k)))) : A.X (i + k)) =
      D i x := sorry

end IsDivisibleBy

end Derivation

end ChainGradedAlgebra
