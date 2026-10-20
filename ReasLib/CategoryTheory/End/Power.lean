/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import ReasLib.CategoryTheory.InverseSystem.Sequential
import Mathlib.Tactic.CrossRefAttribute

/-!
# Towers of powers of a categorical endomorphism

This is the representation-independent owner for kernels, cokernels, and two-term complexes built
from powers of an arbitrary endomorphism.  Scalar principal-power constructions are a specialization
of this API; no ring action is required here.

@stack 0H3D
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w

namespace CategoryTheory.End.Power

variable {C : Type u} [Category.{v} C]

/-- The arrow given by the `(n+1)`st power of an endomorphism. -/
@[stacks 0H3D "endomorphism power arrow stage"]
abbrev arrowStage {M : C} (f : End M) (n : ℕ) : Arrow C :=
  Arrow.mk (f ^ (n + 1))

/-- The commutative square from `f^(n+2)` to `f^(n+1)` with sides `f` and `𝟙`. -/
@[stacks 0H3D "endomorphism power lowering square"]
theorem stepSquare_comm {M : C} (f : End M) (n : ℕ) :
    f ≫ (f ^ (n + 1)) = (f ^ (n + 2)) ≫ 𝟙 M := sorry

/-- The arrow-category transition between consecutive positive powers of an endomorphism. -/
@[stacks 0H3D "endomorphism power lowering square morphism"]
noncomputable def stepSquare {M : C} (f : End M) (n : ℕ) :
    arrowStage f (n + 1) ⟶ arrowStage f n :=
  Arrow.homMk' f (𝟙 M) (stepSquare_comm f n)

/-- The inverse system of arrows formed by the positive powers of an endomorphism. -/
@[stacks 0H3D "endomorphism power arrow system"]
abbrev arrowSystem {M : C} (f : End M) : SequentialInverseSystem (Arrow C) :=
  Functor.ofOpSequence (stepSquare f)

/-- The object at stage `n` of the inverse system of power arrows. -/
@[simp, stacks 0H3D "endomorphism power arrow system object"]
theorem arrowSystem_obj {M : C} (f : End M) (n : ℕ) :
    (arrowSystem f).obj (op n) = arrowStage f n := sorry

/-- The successor map of the inverse system of power arrows. -/
@[simp, stacks 0H3D "endomorphism power arrow system transition"]
theorem arrowSystem_stepMap {M : C} (f : End M) (n : ℕ) :
    (arrowSystem f).stepMap n = stepSquare f n := sorry

/-- The commutative square from `f^(n+1)` to `f^(n+2)` with sides `𝟙` and `f`. -/
@[stacks 0H3D "endomorphism power raising square"]
theorem raiseSquare_comm {M : C} (f : End M) (n : ℕ) :
    𝟙 M ≫ (f ^ (n + 2)) = (f ^ (n + 1)) ≫ f := sorry

/-- The arrow-category map from one positive power of an endomorphism to the next. -/
@[stacks 0H3D "endomorphism power raising square morphism"]
noncomputable def raiseSquare {M : C} (f : End M) (n : ℕ) :
    arrowStage f n ⟶ arrowStage f (n + 1) :=
  Arrow.homMk' (𝟙 M) f (raiseSquare_comm f n)

/-- The direct system of arrows formed by the positive powers of an endomorphism. -/
@[stacks 0H3D "endomorphism power arrow direct system"]
abbrev arrowDirectSystem {M : C} (f : End M) : ℕ ⥤ Arrow C :=
  Functor.ofSequence (raiseSquare f)

/-- The object at stage `n` of the direct system of power arrows. -/
@[simp, stacks 0H3D "endomorphism power arrow direct system object"]
theorem arrowDirectSystem_obj {M : C} (f : End M) (n : ℕ) :
    (arrowDirectSystem f).obj n = arrowStage f n := sorry

/-- The successor map of the direct system of power arrows. -/
@[simp, stacks 0H3D "endomorphism power arrow direct system transition"]
theorem arrowDirectSystem_map_succ {M : C} (f : End M) (n : ℕ) :
    (arrowDirectSystem f).map (homOfLE (Nat.le_succ n)) = raiseSquare f n := sorry

section ZeroMorphisms

variable [HasZeroMorphisms C]

/-- The kernel stage associated to the `(n+1)`st power of an endomorphism. -/
@[stacks 0H3D "endomorphism power kernel stage"]
abbrev kernelStage [HasKernels C] {M : C} (f : End M) (n : ℕ) : C :=
  kernel (f ^ (n + 1))

/-- The power-kernel successor relation. -/
@[stacks 0H3D "endomorphism power kernel zero relation"]
theorem kernelStep_zero [HasKernels C] {M : C} (f : End M) (n : ℕ) :
    (kernel.ι (f ^ (n + 2)) ≫ f) ≫ (f ^ (n + 1)) = 0 := sorry

/-- The transition from the kernel of `f^(n+2)` to the kernel of `f^(n+1)`, obtained by
functoriality of kernels. -/
@[stacks 0H3D "endomorphism power kernel transition"]
noncomputable abbrev kernelStep [HasKernels C] {M : C} (f : End M) (n : ℕ) :
    kernelStage f (n + 1) ⟶ kernelStage f n :=
  (Limits.ker C).map (stepSquare f n)

/-- The kernel transition is characterized after composing with the kernel inclusion. -/
@[simp, reassoc, stacks 0H3D "endomorphism power kernel transition factorization"]
theorem kernelStep_comp_ι [HasKernels C] {M : C} (f : End M) (n : ℕ) :
    kernelStep f n ≫ kernel.ι (f ^ (n + 1)) =
      kernel.ι (f ^ (n + 2)) ≫ f := sorry

/-- The inverse system of kernels of successive positive powers of an endomorphism. -/
@[stacks 0H3D "endomorphism power kernel system"]
abbrev kernelSystem [HasKernels C] {M : C} (f : End M) : SequentialInverseSystem C :=
  arrowSystem f ⋙ Limits.ker C

/-- The object at stage `n` of the inverse system of power kernels. -/
@[simp, stacks 0H3D "endomorphism power kernel system object"]
theorem kernelSystem_obj [HasKernels C] {M : C} (f : End M) (n : ℕ) :
    (kernelSystem f).obj (op n) = kernelStage f n := sorry

/-- The successor map of the inverse system of power kernels. -/
@[simp, stacks 0H3D "endomorphism power kernel system transition"]
theorem kernelSystem_stepMap [HasKernels C] {M : C} (f : End M) (n : ℕ) :
    (kernelSystem f).stepMap n = kernelStep f n := sorry

/-- The canonical map from the kernel of `f^(n+1)` to the kernel of `f^(n+2)`. -/
@[stacks 0H3D "endomorphism power kernel raising map"]
noncomputable abbrev kernelRaise [HasKernels C] {M : C} (f : End M) (n : ℕ) :
    kernelStage f n ⟶ kernelStage f (n + 1) :=
  (Limits.ker C).map (raiseSquare f n)

/-- The raising map is characterized after composing with the next kernel inclusion. -/
@[simp, reassoc, stacks 0H3D "endomorphism power kernel raising factorization"]
theorem kernelRaise_comp_ι [HasKernels C] {M : C} (f : End M) (n : ℕ) :
    kernelRaise f n ≫ kernel.ι (f ^ (n + 2)) = kernel.ι (f ^ (n + 1)) := sorry

/-- The direct system of kernels of successive positive powers of an endomorphism. -/
@[stacks 0H3D "endomorphism power kernel direct system"]
abbrev kernelDirectSystem [HasKernels C] {M : C} (f : End M) : ℕ ⥤ C :=
  arrowDirectSystem f ⋙ Limits.ker C

/-- The object at stage `n` of the direct system of power kernels. -/
@[simp, stacks 0H3D "endomorphism power kernel direct system object"]
theorem kernelDirectSystem_obj [HasKernels C] {M : C} (f : End M) (n : ℕ) :
    (kernelDirectSystem f).obj n = kernelStage f n := sorry

/-- The successor map of the direct system of power kernels. -/
@[simp, stacks 0H3D "endomorphism power kernel direct system transition"]
theorem kernelDirectSystem_map_succ [HasKernels C] {M : C} (f : End M) (n : ℕ) :
    (kernelDirectSystem f).map (homOfLE (Nat.le_succ n)) = kernelRaise f n := sorry

/-- The quotient stage associated to the `(n+1)`st power of an endomorphism. -/
@[stacks 0H3D "endomorphism power quotient stage"]
abbrev quotientStage [HasCokernels C] {M : C} (f : End M) (n : ℕ) : C :=
  cokernel (f ^ (n + 1))

/-- The power-quotient successor relation. -/
@[stacks 0H3D "endomorphism power quotient zero relation"]
theorem quotientStep_zero [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    (f ^ (n + 2)) ≫ cokernel.π (f ^ (n + 1)) = 0 := sorry

/-- The transition from the quotient by `f^(n+2)` to the quotient by `f^(n+1)`, obtained by
functoriality of cokernels. -/
@[stacks 0H3D "endomorphism power quotient transition"]
noncomputable abbrev quotientStep [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    quotientStage f (n + 1) ⟶ quotientStage f n :=
  (Limits.coker C).map (stepSquare f n)

/-- The quotient transition is characterized by the cokernel projections. -/
@[simp, reassoc, stacks 0H3D "endomorphism power quotient transition factorization"]
theorem quotientStep_comp_π [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    cokernel.π (f ^ (n + 2)) ≫ quotientStep f n = cokernel.π (f ^ (n + 1)) := sorry

/-- The forward quotient map induced by one further multiplication by `f`. -/
@[stacks 0H3D "endomorphism power quotient raising zero relation"]
theorem quotientRaise_zero [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    (f ^ (n + 1)) ≫ f ≫ cokernel.π (f ^ (n + 2)) = 0 := sorry

/-- The forward quotient map induced by one further multiplication by `f`. -/
@[stacks 0H3D "endomorphism power quotient raising map"]
noncomputable def quotientRaise [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    quotientStage f n ⟶ quotientStage f (n + 1) :=
  (Limits.coker C).map (raiseSquare f n)

/-- The quotient projection characterizes the raising map. -/
@[simp, reassoc, stacks 0H3D "endomorphism power quotient raising factorization"]
theorem quotientProjection_comp_raise [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    cokernel.π (f ^ (n + 1)) ≫ quotientRaise f n =
      f ≫ cokernel.π (f ^ (n + 2)) := sorry

/-- The square expressing that an endomorphism commutes with each of its powers. -/
@[stacks 0H3D "endomorphism power action square"]
theorem quotientActionSquare_comm [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    f ≫ (f ^ (n + 1)) = (f ^ (n + 1)) ≫ f := sorry

/-- The endomorphism square on the `(n+1)`st power arrow. -/
@[stacks 0H3D "endomorphism power action square morphism"]
noncomputable def quotientActionSquare [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    arrowStage f n ⟶ arrowStage f n :=
  Arrow.homMk' f f (quotientActionSquare_comm f n)

/-- The endomorphism induced by `f` on the cokernel of `f^(n+1)`. -/
@[stacks 0H3D "endomorphism power quotient action"]
noncomputable abbrev quotientAction [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    quotientStage f n ⟶ quotientStage f n :=
  (Limits.coker C).map (quotientActionSquare f n)

/-- The quotient projection characterizes the induced endomorphism action. -/
@[simp, reassoc, stacks 0H3D "endomorphism power quotient action factorization"]
theorem quotientProjection_comp_action [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    cokernel.π (f ^ (n + 1)) ≫ quotientAction f n =
      f ≫ cokernel.π (f ^ (n + 1)) := sorry

/-- Raising and then lowering a quotient stage is the induced action of `f`. -/
@[reassoc, stacks 0H3D "endomorphism power quotient raise-lower action"]
theorem quotientRaise_comp_step [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    quotientRaise f n ≫ quotientStep f n = quotientAction f n := sorry

/-- Lowering and then raising a quotient stage is the induced action of `f` on the next stage. -/
@[reassoc, stacks 0H3D "endomorphism power quotient lower-raise action"]
theorem quotientStep_comp_raise [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    quotientStep f n ≫ quotientRaise f n = quotientAction f (n + 1) := sorry

/-- The inverse system of successive power quotients. -/
@[stacks 0H3D "endomorphism power quotient system"]
abbrev quotientSystem [HasCokernels C] {M : C} (f : End M) : SequentialInverseSystem C :=
  arrowSystem f ⋙ Limits.coker C

/-- The object at stage `n` of the inverse system of power quotients. -/
@[simp, stacks 0H3D "endomorphism power quotient system object"]
theorem quotientSystem_obj [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    (quotientSystem f).obj (op n) = quotientStage f n := sorry

/-- The successor map of the inverse system of power quotients. -/
@[simp, stacks 0H3D "endomorphism power quotient system transition"]
theorem quotientSystem_stepMap [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    (quotientSystem f).stepMap n = quotientStep f n := sorry

/-- The direct system of successive power quotients and the raising maps. -/
@[stacks 0H3D "endomorphism power quotient direct system"]
abbrev quotientDirectSystem [HasCokernels C] {M : C} (f : End M) : ℕ ⥤ C :=
  arrowDirectSystem f ⋙ Limits.coker C

/-- The object at stage `n` of the direct system of power quotients. -/
@[simp, stacks 0H3D "endomorphism power quotient direct system object"]
theorem quotientDirectSystem_obj [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    (quotientDirectSystem f).obj n = quotientStage f n := sorry

/-- The successor map of the direct system of power quotients. -/
@[simp, stacks 0H3D "endomorphism power quotient direct system transition"]
theorem quotientDirectSystem_map_succ [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    (quotientDirectSystem f).map (homOfLE (Nat.le_succ n)) = quotientRaise f n := sorry

/-- The short complex formed by the power endomorphism and its cokernel projection. -/
@[stacks 0H3D "endomorphism power quotient row"]
abbrev quotientRow [HasCokernels C] {M : C} (f : End M) (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (f ^ (n + 1)) (cokernel.π (f ^ (n + 1)))
    (cokernel.condition (f ^ (n + 1)))

/-- Commutativity of the first square in the transition between consecutive quotient rows. -/
@[stacks 0H3D "endomorphism power quotient row first square"]
theorem rowStep_comm₁₂ [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    f ≫ (f ^ (n + 1)) = (f ^ (n + 2)) ≫ 𝟙 M := sorry

/-- Commutativity of the second square in the transition between consecutive quotient rows. -/
@[stacks 0H3D "endomorphism power quotient row second square"]
theorem rowStep_comm₂₃ [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    𝟙 M ≫ cokernel.π (f ^ (n + 1)) =
      cokernel.π (f ^ (n + 2)) ≫ quotientStep f n := sorry

/-- The morphism from the `(n+1)`st quotient row to the `n`th quotient row. -/
@[stacks 0H3D "endomorphism power quotient row transition"]
noncomputable def rowStep [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    quotientRow f (n + 1) ⟶ quotientRow f n :=
  ShortComplex.homMk f (𝟙 M) (quotientStep f n)
    (rowStep_comm₁₂ f n) (rowStep_comm₂₃ f n)

/-- The left component of the transition between consecutive quotient rows. -/
@[simp, stacks 0H3D "endomorphism power quotient row transition left component"]
theorem rowStep_τ₁ [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    (rowStep f n).τ₁ = f := sorry

/-- The middle component of the transition between consecutive quotient rows. -/
@[simp, stacks 0H3D "endomorphism power quotient row transition middle component"]
theorem rowStep_τ₂ [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    (rowStep f n).τ₂ = 𝟙 M := sorry

/-- The right component of the transition between consecutive quotient rows. -/
@[simp, stacks 0H3D "endomorphism power quotient row transition right component"]
theorem rowStep_τ₃ [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    (rowStep f n).τ₃ = quotientStep f n := sorry

/-- The inverse system of short complexes consisting of the endomorphism power quotient rows. -/
@[stacks 0H3D "endomorphism power quotient row system"]
abbrev rowSystem [HasCokernels C] {M : C} (f : End M) :
    SequentialInverseSystem (ShortComplex C) :=
  Functor.ofOpSequence (rowStep f)

/-- The object at stage `n` of the inverse system of quotient rows. -/
@[simp, stacks 0H3D "endomorphism power quotient row system object"]
theorem rowSystem_obj [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    (rowSystem f).obj (op n) = quotientRow f n := sorry

/-- The successor map of the inverse system of quotient rows. -/
@[simp, stacks 0H3D "endomorphism power quotient row system transition"]
theorem rowSystem_stepMap [HasCokernels C] {M : C} (f : End M) (n : ℕ) :
    (rowSystem f).stepMap n = rowStep f n := sorry

end ZeroMorphisms

section Abelian

variable [Abelian C]

/-- Stabilization of the kernel subobjects of the positive powers of an endomorphism. -/
@[stacks 0H3D "endomorphism power kernel stabilization"]
def kernelStabilizes {M : C} (f : End M) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ,
    kernelSubobject (f ^ (n + c + 1)) = kernelSubobject (f ^ (c + 1))

/-- The kernel-subobject equality required at a fixed stabilization cutoff. -/
@[stacks 0H3D "endomorphism power kernel stability at a cutoff"]
def kernelStableAt {M : C} (f : End M) (c : ℕ) : Prop :=
  ∀ n : ℕ, kernelSubobject (f ^ (n + c + 1)) = kernelSubobject (f ^ (c + 1))

/-- Kernel stabilization is the existence of a cutoff satisfying `kernelStableAt`. -/
@[stacks 0H3D "endomorphism power kernel stabilization witness"]
theorem kernelStabilizes_iff {M : C} (f : End M) :
    kernelStabilizes f ↔ ∃ c : ℕ, kernelStableAt f c := sorry

/-- A fixed stabilized cutoff controls every later positive power, including the successor tail. -/
@[stacks 0H3D "successor tail at a stabilized endomorphism cutoff"]
theorem kernelStableAt_succ {M : C} (f : End M) {c : ℕ}
    (h : kernelStableAt f c) :
    ∀ n : ℕ,
      kernelSubobject (f ^ (n + c + 2)) = kernelSubobject (f ^ (c + 1)) := sorry

/-- A stabilized kernel cutoff also controls the successor tail. -/
@[stacks 0H3D "successor of a stabilized endomorphism kernel tail"]
theorem kernelStabilizes_succ {M : C} (f : End M)
    (h : kernelStabilizes f) :
    ∃ c : ℕ, ∀ n : ℕ,
      kernelSubobject (f ^ (n + c + 2)) = kernelSubobject (f ^ (c + 1)) := sorry

end Abelian

end CategoryTheory.End.Power
