module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.CategoryTheory.InverseSystem.Sequential.PrincipalTorsion.Power
public import ReasLib.CategoryTheory.Linear.PrincipalPower
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quotient presentations of principal torsion systems

The quotient condition in the principal-torsion characterization is represented by a shifted
inverse system isomorphism
`F.shift 1 ≅ quotientSystem r M`, where the latter has stage `n` equal to
`coker (r^(n+1) : M ⟶ M)`.  This keeps the one-based source indexing out of the canonical
quotient construction while exposing the stagewise row API through `PrincipalPower`. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w u' v'

namespace CategoryTheory.SequentialInverseSystem.PrincipalTorsion

variable {R : Type w} [CommSemiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C] [HasCokernels C]

/-- A chosen realization of the tail of `F` by quotients of a torsion-free object. -/
@[stacks 0H39 "torsion-free principal-power quotient presentation"]
structure QuotientPresentation (r : R) (F : SequentialInverseSystem C) where
  /-- The ambient object whose power quotients realize the tower. -/
  object : C
  /-- Multiplication by `r` on the ambient object is monomorphic. -/
  torsionFree : CategoryTheory.Linear.PrincipalPower.IsTorsionFree r object
  /-- The shifted system is the canonical principal-power quotient system. -/
  shiftIso : F.shift 1 ≅ CategoryTheory.Linear.PrincipalPower.quotientSystem r object

/-- A torsion-free object and an isomorphism of its power-quotient system with the positive
tail determine a quotient presentation. -/
def QuotientPresentation.ofIso {r : R} {F : SequentialInverseSystem C}
    (object : C) (h_torsionFree : CategoryTheory.Linear.PrincipalPower.IsTorsionFree r object)
    (shiftIso : F.shift 1 ≅ CategoryTheory.Linear.PrincipalPower.quotientSystem r object) :
    QuotientPresentation r F :=
  { object := object
    torsionFree := h_torsionFree
    shiftIso := shiftIso }

/-- The stagewise isomorphism supplied by a quotient presentation. -/
@[stacks 0H39 "quotient presentation stage isomorphism"]
abbrev QuotientPresentation.stageIso
    {r : R} {F : SequentialInverseSystem C}
    (P : QuotientPresentation r F) (n : ℕ) :
    (F.shift 1).obj (op n) ≅
      CategoryTheory.Linear.PrincipalPower.quotientStage r P.object n :=
  P.shiftIso.app (op n)

/-- A sequential inverse system is obtained from the quotients of an `r`-torsion-free object. -/
@[stacks 0H39 "existence of a torsion-free principal-power quotient presentation"]
def IsQuotientPresented (r : R) (F : SequentialInverseSystem C) : Prop :=
  Nonempty (QuotientPresentation r F)

/-- A quotient presentation exists exactly when the positive tail is isomorphic to the
power-quotient system of a torsion-free object. -/
theorem isQuotientPresented_iff (r : R) (F : SequentialInverseSystem C) :
    IsQuotientPresented r F ↔
      ∃ G : C, CategoryTheory.Linear.PrincipalPower.IsTorsionFree r G ∧
        Nonempty (F.shift 1 ≅ CategoryTheory.Linear.PrincipalPower.quotientSystem r G) := sorry

section Abelian

variable {R : Type w} [CommRing R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

/-- A quotient presentation supplies the short exact power rows. -/
@[stacks 0H39 "quotient presentation gives power presentation"]
theorem isPowerPresented_of_isQuotientPresented
    (r : R) (F : SequentialInverseSystem C) :
    IsQuotientPresented r F → IsPowerPresented r F := sorry

end Abelian

end CategoryTheory.SequentialInverseSystem.PrincipalTorsion
