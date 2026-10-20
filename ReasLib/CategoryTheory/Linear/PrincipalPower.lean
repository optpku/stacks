/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Data.PNat.Order
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.Epi
import Mathlib.Tactic.CrossRefAttribute

/-!
# Principal-power towers in a linear category

For an object `M` of an `R`-linear category and `f : R`, the powers of the scalar endomorphism
`f • 𝟙 M` give canonical kernel and cokernel towers.  This is the category-theoretic owner;
module torsion submodules and quotient modules are concrete views of these objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w u' v'

namespace CategoryTheory.Linear.PrincipalPower

variable {R : Type w} [CommSemiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- The endomorphism of `M` given by the `n`th power of a scalar. -/
@[stacks 0H3A "categorical principal-power endomorphism"]
abbrev smulPow (f : R) (M : C) (n : ℕ) : M ⟶ M :=
  (f ^ n) • 𝟙 M

/-- Multiplication by `f` followed by multiplication by `f^n` is multiplication by
`f^(n+1)`. -/
@[stacks 0H3A "categorical principal-power composition"]
theorem smul_comp_smulPow (f : R) (M : C) (n : ℕ) :
    (f • 𝟙 M) ≫ smulPow f M n = smulPow f M (n + 1) := sorry

/-- Multiplication by `f^n` followed by multiplication by `f` is multiplication by `f^(n+1)`. -/
@[stacks 0H3A "categorical principal-power composition on the right"]
theorem smulPow_comp_smul (f : R) (M : C) (n : ℕ) :
    smulPow f M n ≫ (f • 𝟙 M) = smulPow f M (n + 1) := sorry

/-- The zeroth scalar power is the identity endomorphism. -/
@[simp, stacks 0H3A "zeroth categorical principal power"]
theorem smulPow_zero (f : R) (M : C) :
    smulPow f M 0 = 𝟙 M := sorry

/-- Scalar powers are natural in the acted-on object. -/
@[simp, reassoc, stacks 0H3A "naturality of categorical principal powers"]
theorem smulPow_natural (f : R) {M N : C} (φ : M ⟶ N) (n : ℕ) :
    smulPow f M n ≫ φ = φ ≫ smulPow f N n := sorry

/-- The kernel of multiplication by `f^(n+1)`. -/
@[stacks 0H3A "categorical principal-power kernel stage"]
abbrev kernelStage [HasKernels C] (f : R) (M : C) (n : ℕ) : C :=
  kernel (smulPow f M (n + 1))

/-- Multiplication by `f` carries the `(n+2)`nd power kernel into the `(n+1)`st power kernel. -/
@[stacks 0H3A "categorical principal-power kernel zero relation"]
theorem kernelStep_zero [HasKernels C] (f : R) (M : C) (n : ℕ) :
    (kernel.ι (smulPow f M (n + 2)) ≫ (f • 𝟙 M)) ≫ smulPow f M (n + 1) = 0 :=
  sorry

/-- The successor transition in the principal-power kernel tower. -/
@[stacks 0H3A "categorical principal-power kernel transition"]
abbrev kernelStep [HasKernels C] (f : R) (M : C) (n : ℕ) :
    kernelStage f M (n + 1) ⟶ kernelStage f M n :=
  kernel.lift (smulPow f M (n + 1))
    (kernel.ι (smulPow f M (n + 2)) ≫ (f • 𝟙 M))
    (kernelStep_zero f M n)

/-- The principal-power kernel transition factors through the next kernel inclusion. -/
@[simp, reassoc, stacks 0H3A "principal-power kernel transition factorization"]
theorem kernelStep_comp_ι [HasKernels C] (f : R) (M : C) (n : ℕ) :
    kernelStep f M n ≫ kernel.ι (smulPow f M (n + 1)) =
      kernel.ι (smulPow f M (n + 2)) ≫ (f • 𝟙 M) := sorry

/-- The sequential inverse system of kernels of positive powers of `f`. -/
@[stacks 0H3A "categorical principal-power kernel system"]
abbrev kernelSystem [HasKernels C] (f : R) (M : C) : SequentialInverseSystem C :=
  Functor.ofOpSequence (kernelStep f M)

/-- The object at stage `n` of the principal-power kernel system. -/
@[simp, stacks 0H3A "principal-power kernel system object"]
theorem kernelSystem_obj [HasKernels C] (f : R) (M : C) (n : ℕ) :
    (kernelSystem f M).obj (op n) = kernelStage f M n := sorry

/-- The successor transition exposed through the sequential-system API. -/
@[simp, stacks 0H3A "principal-power kernel system transition"]
theorem kernelSystem_stepMap [HasKernels C] (f : R) (M : C) (n : ℕ) :
    (kernelSystem f M).stepMap n = kernelStep f M n := sorry

/- The kernel tower is indexed from `0`, while source-style rows start at the positive stage `1`.
These accessors expose the canonical map from the first kernel stage to every later stage. -/

/-- The defining composite for the canonical kernel inclusion `K 0 ⟶ K n` vanishes. -/
@[stacks 0H3A "categorical principal-power kernel inclusion zero relation"]
theorem kernelInclusion_zero [HasKernels C] (f : R) (M : C) (n : ℕ+) :
    kernel.ι (smulPow f M 1) ≫ smulPow f M ((n : ℕ) + 1) = 0 := sorry

/-- The canonical inclusion of the first power-kernel stage into the `n`th stage. -/
@[stacks 0H3A "categorical principal-power kernel inclusion"]
noncomputable def kernelInclusion [HasKernels C]
    (f : R) (M : C) (n : ℕ+) :
    kernelStage f M 0 ⟶ kernelStage f M (n : ℕ) :=
  kernel.lift (smulPow f M ((n : ℕ) + 1))
    (kernel.ι (smulPow f M 1)) (kernelInclusion_zero f M n)

/-- The kernel inclusion is characterized after embedding into the ambient object. -/
@[simp, reassoc, stacks 0H3A "principal-power kernel inclusion factorization"]
theorem kernelInclusion_comp_ι [HasKernels C] (f : R) (M : C) (n : ℕ+) :
    kernelInclusion f M n ≫ kernel.ι (smulPow f M ((n : ℕ) + 1)) =
      kernel.ι (smulPow f M 1) := sorry

/-- The stage equality needed to view the predecessor transition as a map out of `K n`. -/
@[stacks 0H3A "principal-power kernel predecessor stage equality"]
theorem kernelStage_pred_succ [HasKernels C] (f : R) (M : C) (n : ℕ+) :
    kernelStage f M (n : ℕ) =
      kernelStage f M ((n : ℕ) - 1 + 1) := sorry

/-- The source-style transition `K n ⟶ K (n - 1)` on positive kernel stages. -/
@[stacks 0H3A "principal-power kernel predecessor transition"]
noncomputable def kernelTransition [HasKernels C]
    (f : R) (M : C) (n : ℕ+) :
    kernelStage f M (n : ℕ) ⟶ kernelStage f M ((n : ℕ) - 1) :=
  eqToHom (kernelStage_pred_succ f M n) ≫ kernelStep f M ((n : ℕ) - 1)

/-- The first kernel inclusion is killed by the predecessor transition. -/
@[reassoc, stacks 0H3A "principal-power kernel inclusion transition zero"]
theorem kernelInclusion_comp_transition_zero [HasKernels C]
    (f : R) (M : C) (n : ℕ+) :
    kernelInclusion f M n ≫ kernelTransition f M n = 0 := sorry

/-- The source-style kernel row `K 0 ⟶ K n ⟶ K (n-1)`. -/
@[stacks 0H3A "categorical principal-power kernel row"]
abbrev kernelRow [HasKernels C] (f : R) (M : C) (n : ℕ+) : ShortComplex C :=
  ShortComplex.mk
    (kernelInclusion f M n)
    (kernelTransition f M n)
    (kernelInclusion_comp_transition_zero f M n)

/-- Every kernel row is short exact when multiplication by `f` is epimorphic. -/
@[stacks 0H3A "principal-power kernel row short exact"]
theorem kernelRow_shortExact
    {D : Type u'} [Category.{v'} D] [Abelian D] [Linear R D]
    (f : R) (M : D) [Epi (f • 𝟙 M)] (n : ℕ+) :
    (kernelRow f M n).ShortExact := sorry

/-- The predecessor map in a principal-power kernel row is epimorphic. -/
@[stacks 0H3A "principal-power kernel transition epimorphism"]
noncomputable instance kernelTransition_epi
    {D : Type u'} [Category.{v'} D] [Abelian D] [Linear R D]
    (f : R) (M : D) [Epi (f • 𝟙 M)] (n : ℕ+) :
    Epi (kernelTransition f M n) :=
  (kernelRow_shortExact f M n).epi_g

/-- The cokernel of multiplication by `f^(n+1)`. -/
@[stacks 0H3A "categorical principal-power quotient stage"]
abbrev quotientStage [HasCokernels C] (f : R) (M : C) (n : ℕ) : C :=
  cokernel (smulPow f M (n + 1))

/-- Multiplication by `f^(n+2)` vanishes in the quotient by `f^(n+1)`. -/
@[stacks 0H3A "categorical principal-power quotient zero relation"]
theorem quotientStep_zero [HasCokernels C] (f : R) (M : C) (n : ℕ) :
    smulPow f M (n + 2) ≫ cokernel.π (smulPow f M (n + 1)) = 0 := sorry

/-- The successor transition in the principal-power quotient tower. -/
@[stacks 0H3A "categorical principal-power quotient transition"]
abbrev quotientStep [HasCokernels C] (f : R) (M : C) (n : ℕ) :
    quotientStage f M (n + 1) ⟶ quotientStage f M n :=
  cokernel.desc (smulPow f M (n + 2))
    (cokernel.π (smulPow f M (n + 1))) (quotientStep_zero f M n)

/-- The principal-power quotient transition is characterized by the quotient projections. -/
@[simp, reassoc, stacks 0H3A "principal-power quotient transition factorization"]
theorem quotientStep_comp_π [HasCokernels C] (f : R) (M : C) (n : ℕ) :
    cokernel.π (smulPow f M (n + 2)) ≫ quotientStep f M n =
      cokernel.π (smulPow f M (n + 1)) := sorry

/-- The defining composite for the forward quotient map vanishes. -/
@[stacks 0H3A "categorical principal-power quotient raising zero relation"]
theorem quotientRaise_zero [HasCokernels C] (f : R) (M : C) (n : ℕ) :
    smulPow f M (n + 1) ≫ (f • 𝟙 M) ≫
        cokernel.π (smulPow f M (n + 2)) = 0 := sorry

/-- The forward quotient map induced by multiplication by `f`. -/
@[stacks 0H3A "categorical principal-power quotient raising map"]
noncomputable def quotientRaise [HasCokernels C] (f : R) (M : C) (n : ℕ) :
    quotientStage f M n ⟶ quotientStage f M (n + 1) :=
  cokernel.desc (smulPow f M (n + 1))
    ((f • 𝟙 M) ≫ cokernel.π (smulPow f M (n + 2)))
    (quotientRaise_zero f M n)

/-- The quotient projection characterizes the forward quotient map. -/
@[simp, reassoc, stacks 0H3A "principal-power quotient raising factorization"]
theorem quotientProjection_comp_raise [HasCokernels C] (f : R) (M : C) (n : ℕ) :
    cokernel.π (smulPow f M (n + 1)) ≫ quotientRaise f M n =
      (f • 𝟙 M) ≫ cokernel.π (smulPow f M (n + 2)) := sorry

/-- Raising and then lowering a quotient stage is scalar multiplication by `f`. -/
@[reassoc, stacks 0H3A "principal-power quotient raise-lower composition"]
theorem quotientRaise_comp_step [HasCokernels C]
    (f : R) (M : C) (n : ℕ) :
    quotientRaise f M n ≫ quotientStep f M n =
      f • 𝟙 (quotientStage f M n) := sorry

/-- Lowering and then raising a quotient stage is scalar multiplication by `f`. -/
@[reassoc, stacks 0H3A "principal-power quotient lower-raise composition"]
theorem quotientStep_comp_raise [HasCokernels C]
    (f : R) (M : C) (n : ℕ) :
    quotientStep f M n ≫ quotientRaise f M n =
      f • 𝟙 (quotientStage f M (n + 1)) := sorry

/-- The direct system of positive-power quotients and the maps induced by multiplication by `f`. -/
@[stacks 0H39 "principal-power quotient direct system"]
abbrev quotientDirectSystem [HasCokernels C] (f : R) (M : C) : ℕ ⥤ C :=
  Functor.ofSequence (quotientRaise f M)

@[simp, stacks 0H39 "principal-power quotient direct system object"]
theorem quotientDirectSystem_obj [HasCokernels C] (f : R) (M : C) (n : ℕ) :
    (quotientDirectSystem f M).obj n = quotientStage f M n := sorry

@[simp, stacks 0H39 "principal-power quotient direct system transition"]
theorem quotientDirectSystem_map_succ [HasCokernels C] (f : R) (M : C) (n : ℕ) :
    (quotientDirectSystem f M).map (homOfLE (Nat.le_succ n)) = quotientRaise f M n := sorry

/-- The sequential inverse system of cokernels of positive powers of `f`. -/
@[stacks 0H3A "categorical principal-power quotient system"]
abbrev quotientSystem [HasCokernels C] (f : R) (M : C) : SequentialInverseSystem C :=
  Functor.ofOpSequence (quotientStep f M)

/-- The object at stage `n` of the principal-power quotient system. -/
@[simp, stacks 0H3A "principal-power quotient system object"]
theorem quotientSystem_obj [HasCokernels C] (f : R) (M : C) (n : ℕ) :
    (quotientSystem f M).obj (op n) = quotientStage f M n := sorry

/-- The successor transition exposed through the sequential-system API. -/
@[simp, stacks 0H3A "principal-power quotient system transition"]
theorem quotientSystem_stepMap [HasCokernels C] (f : R) (M : C) (n : ℕ) :
    (quotientSystem f M).stepMap n = quotientStep f M n := sorry

/- The quotient tower is indexed from `0`, whereas source-style principal torsion towers start at
`1`.  These maps expose the canonical arrow from `Q 0` to `Q n` without introducing a second
shifted tower. -/

/-- The defining composite for the canonical inclusion `Q 0 ⟶ Q n` vanishes. -/
@[stacks 0H3A "categorical principal-power quotient inclusion zero relation"]
theorem quotientInclusion_zero [HasCokernels C] (f : R) (M : C) (n : ℕ+) :
    smulPow f M 1 ≫ smulPow f M (n : ℕ) ≫
        cokernel.π (smulPow f M ((n : ℕ) + 1)) = 0 := sorry

/-- The canonical inclusion of the first quotient stage into the `n`th quotient stage. -/
@[stacks 0H3A "categorical principal-power quotient inclusion"]
noncomputable def quotientInclusion [HasCokernels C]
    (f : R) (M : C) (n : ℕ+) :
    quotientStage f M 0 ⟶ quotientStage f M (n : ℕ) :=
  cokernel.desc (smulPow f M 1)
    (smulPow f M (n : ℕ) ≫ cokernel.π (smulPow f M ((n : ℕ) + 1)))
    (quotientInclusion_zero f M n)

/-- The stage equality needed to view the predecessor transition as a map out of `Q n`. -/
@[stacks 0H3A "principal-power quotient predecessor stage equality"]
theorem quotientStage_pred_succ [HasCokernels C] (f : R) (M : C) (n : ℕ+) :
    quotientStage f M (n : ℕ) =
      quotientStage f M ((n : ℕ) - 1 + 1) := sorry

/-- The source-style transition `Q n ⟶ Q (n - 1)` on positive quotient stages. -/
@[stacks 0H3A "principal-power quotient predecessor transition"]
noncomputable def quotientTransition [HasCokernels C]
    (f : R) (M : C) (n : ℕ+) :
    quotientStage f M (n : ℕ) ⟶ quotientStage f M ((n : ℕ) - 1) :=
  eqToHom (quotientStage_pred_succ f M n) ≫ quotientStep f M ((n : ℕ) - 1)

/-- The quotient projection characterizes the canonical inclusion `Q 0 ⟶ Q n`. -/
@[simp, reassoc, stacks 0H3A "principal-power quotient inclusion factorization"]
theorem quotientProjection_comp_inclusion [HasCokernels C]
    (f : R) (M : C) (n : ℕ+) :
    cokernel.π (smulPow f M 1) ≫ quotientInclusion f M n =
      smulPow f M (n : ℕ) ≫ cokernel.π (smulPow f M ((n : ℕ) + 1)) := sorry

/-- The canonical inclusion `Q 0 ⟶ Q n` is killed by the quotient transition `Q n ⟶ Q (n-1)`. -/
@[reassoc, stacks 0H3A "principal-power quotient inclusion transition zero"]
theorem quotientInclusion_comp_transition_zero [HasCokernels C]
    (f : R) (M : C) (n : ℕ+) :
    quotientInclusion f M n ≫ quotientTransition f M n = 0 := sorry

/-- The inclusions are compatible with consecutive quotient transitions. -/
@[reassoc, stacks 0H3A "principal-power quotient inclusion transition"]
theorem quotientInclusion_succ_comp_transition [HasCokernels C]
    (f : R) (M : C) (n : ℕ+) :
    quotientInclusion f M ⟨(n : ℕ) + 1, Nat.succ_pos _⟩ ≫
        quotientTransition f M ⟨(n : ℕ) + 1, Nat.succ_pos _⟩ =
      quotientInclusion f M n := sorry

/-- The source-style quotient row `Q 0 ⟶ Q n ⟶ Q (n-1)`. -/
@[stacks 0H3A "categorical principal-power quotient row"]
abbrev quotientRow [HasCokernels C] (f : R) (M : C) (n : ℕ+) : ShortComplex C :=
  ShortComplex.mk
    (quotientInclusion f M n)
    (quotientTransition f M n)
    (quotientInclusion_comp_transition_zero f M n)

/-- Every quotient row is short exact when multiplication by `f` is monic. -/
@[stacks 0H3A "principal-power quotient row short exact"]
theorem quotientRow_shortExact
    {D : Type u'} [Category.{v'} D] [Abelian D] [Linear R D]
    (f : R) (M : D) [Mono (f • 𝟙 M)] (n : ℕ+) :
    (quotientRow f M n).ShortExact := sorry

/-- The canonical short complex presenting the quotient by `f^(n+1)`. -/
@[stacks 0H3A "categorical principal-power quotient row"]
abbrev row [HasCokernels C] (f : R) (M : C) (n : ℕ) : ShortComplex C :=
  ShortComplex.mk
    (smulPow f M (n + 1))
    (cokernel.π (smulPow f M (n + 1)))
    (cokernel.condition (smulPow f M (n + 1)))

/-- The left square for the transition between consecutive principal-power quotient rows. -/
@[stacks 0H3A "principal-power quotient row left square"]
theorem rowStep_comm₁₂ [HasCokernels C] (f : R) (M : C) (n : ℕ) :
    (f • 𝟙 M) ≫ (row f M n).f = (row f M (n + 1)).f ≫ 𝟙 M := sorry

/-- The right square for the transition between consecutive principal-power quotient rows. -/
@[stacks 0H3A "principal-power quotient row right square"]
theorem rowStep_comm₂₃ [HasCokernels C] (f : R) (M : C) (n : ℕ) :
    𝟙 M ≫ (row f M n).g =
      (row f M (n + 1)).g ≫ quotientStep f M n := sorry

/-- The morphism from the `(n+1)`st principal-power row to the `n`th row.  Its left component is
multiplication by `f`, its middle component is the identity, and its right component is the
canonical quotient transition. -/
@[stacks 0H3A "transition between principal-power quotient rows"]
noncomputable def rowStep [HasCokernels C] (f : R) (M : C) (n : ℕ) :
    row f M (n + 1) ⟶ row f M n where
  τ₁ := f • 𝟙 M
  τ₂ := 𝟙 M
  τ₃ := quotientStep f M n
  comm₁₂ := rowStep_comm₁₂ f M n
  comm₂₃ := rowStep_comm₂₃ f M n

/-- The left component of the transition between consecutive principal-power rows. -/
@[simp, stacks 0H3A "left component of a principal-power row transition"]
theorem rowStep_τ₁ [HasCokernels C] (f : R) (M : C) (n : ℕ) :
    (rowStep f M n).τ₁ = f • 𝟙 M := sorry

/-- The middle component of the transition between consecutive principal-power rows. -/
@[simp, stacks 0H3A "middle component of a principal-power row transition"]
theorem rowStep_τ₂ [HasCokernels C] (f : R) (M : C) (n : ℕ) :
    (rowStep f M n).τ₂ = 𝟙 M := sorry

/-- The right component of the transition between consecutive principal-power rows. -/
@[simp, stacks 0H3A "right component of a principal-power row transition"]
theorem rowStep_τ₃ [HasCokernels C] (f : R) (M : C) (n : ℕ) :
    (rowStep f M n).τ₃ = quotientStep f M n := sorry

/-- If multiplication by `f` is monic, every principal-power quotient row is short exact. -/
@[stacks 0H3A "principal-power quotient row short exact"]
theorem row_shortExact
    {D : Type u'} [Category.{v'} D] [Abelian D] [Linear R D]
    (f : R) (M : D) [Mono (f • 𝟙 M)] (n : ℕ) :
    (row f M n).ShortExact := sorry

/-- Every successor transition in a categorical principal-power quotient system is epimorphic. -/
@[stacks 0H3A "principal-power quotient transition epimorphism"]
noncomputable instance quotientStep_epi
    {D : Type u'} [Category.{v'} D] [Abelian D] [Linear R D]
    (f : R) (M : D) (n : ℕ) : Epi (quotientStep f M n) := sorry

/-- The categorical principal-power quotient system is Mittag-Leffler. -/
@[stacks 0H3A "Mittag-Leffler categorical principal-power quotient system"]
theorem quotientSystem_isMittagLeffler
    {D : Type u'} [Category.{v'} D] [Abelian D] [Linear R D]
    (f : R) (M : D) : (quotientSystem f M).IsMittagLeffler := sorry

/-- Multiplication by `f` on `M` is epimorphic. -/
@[stacks 0H3A "categorical principal-power divisibility predicate"]
abbrev IsDivisible (f : R) (M : C) : Prop :=
  Epi (f • 𝟙 M)

/-- Multiplication by `f` on `M` is monomorphic. -/
@[stacks 0H3A "categorical principal-power torsion-free predicate"]
abbrev IsTorsionFree (f : R) (M : C) : Prop :=
  Mono (f • 𝟙 M)

/-- Every positive power of a monomorphic scalar action is monomorphic. -/
noncomputable instance smulPow_mono
    (f : R) (M : C) [IsTorsionFree f M] (n : ℕ) :
    Mono (smulPow f M n) := sorry

/-- Every positive power of an epimorphic scalar action is epimorphic. -/
noncomputable instance smulPow_epi
    (f : R) (M : C) [IsDivisible f M] (n : ℕ) :
    Epi (smulPow f M n) := sorry

/-- The principal Tate object, defined as the limit of the positive power-kernel system. -/
@[stacks 0H3A "principal Tate object in a linear category"]
abbrev tateObject [HasKernels C] [HasLimitsOfShape ℕᵒᵖ C]
    (f : R) (M : C) : C :=
  limit (kernelSystem f M)

/- The standard Tate-object notation is owner-scoped because several unrelated Tate
constructions coexist in large developments. -/
scoped[PrincipalPower] notation:max "T[" f "]" M:max =>
  CategoryTheory.Linear.PrincipalPower.tateObject f M

/-- The canonical projection from a principal Tate object to its `n`th power-kernel stage. -/
@[stacks 0H3A "principal Tate object stage projection"]
abbrev tateProjection [HasKernels C] [HasLimitsOfShape ℕᵒᵖ C]
    (f : R) (M : C) (n : ℕ) : tateObject f M ⟶ kernelStage f M n :=
  limit.π (kernelSystem f M) (op n)

/-- Consecutive stage projections from a principal Tate object commute with the kernel
transition. -/
@[stacks 0H3A "compatibility of principal Tate stage projections"]
theorem tateProjection_comp_kernelStep
    [HasKernels C] [HasLimitsOfShape ℕᵒᵖ C]
    (f : R) (M : C) (n : ℕ) :
    tateProjection f M (n + 1) ≫ kernelStep f M n =
      tateProjection f M n := sorry

end CategoryTheory.Linear.PrincipalPower
