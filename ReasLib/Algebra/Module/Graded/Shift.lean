/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Graded.Bimodule.Category
public import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Tactic.CrossRefAttribute

/-!
# Shifts of graded modules and bimodules

The grading shift is constructed for right modules over any additively graded algebra. For a
left module over an integer-graded algebra, the shift additionally pulls the action back along
the Koszul sign automorphism. These two constructions induce the corresponding shifts of graded
bimodules.
-/

@[expose] public section

noncomputable section

universe x y w v u

open scoped DirectSum
open CategoryTheory

namespace GradedModule

section Grading

variable {ι : Type x} [AddGroup ι]
variable {R : Type u} [Semiring R]
variable {M : Type y} [AddCommMonoid M] [Module R M]

/-- Reindex an internal grading by translation, so that shifted degree `n` is original degree
`n + k`. -/
def shiftGrading (𝓜 : ι → Submodule R M) (k : ι) : ι → Submodule R M :=
  fun n ↦ 𝓜 ((Equiv.addRight (-k)).symm n)

/-- A translated grading evaluates in degree `n` as the original grading in degree `n + k`. -/
@[simp]
theorem shiftGrading_apply (𝓜 : ι → Submodule R M) (k n : ι) :
    shiftGrading 𝓜 k n = 𝓜 (n + k) := sorry

/-- Membership in a translated grading is membership in the corresponding original degree. -/
@[simp]
theorem mem_shiftGrading_iff (𝓜 : ι → Submodule R M) (k n : ι) {x : M} :
    x ∈ shiftGrading 𝓜 k n ↔ x ∈ 𝓜 (n + k) := sorry

/-- Translating an internal grading by zero leaves it unchanged. -/
@[simp]
theorem shiftGrading_zero (𝓜 : ι → Submodule R M) : shiftGrading 𝓜 0 = 𝓜 := sorry

/-- Successive translations of an internal grading add their degrees. -/
@[simp]
theorem shiftGrading_add (𝓜 : ι → Submodule R M) (k l : ι) :
    shiftGrading (shiftGrading 𝓜 k) l = shiftGrading 𝓜 (k + l) := sorry

variable [DecidableEq ι]

/-- The decomposition map for a translated grading, obtained by reindexing the original direct
sum decomposition. -/
def shiftDecompose (𝓜 : ι → Submodule R M) [DirectSum.Decomposition 𝓜] (k : ι) :
    M →ₗ[R] (⨁ n : ι, shiftGrading 𝓜 k n) :=
  (DirectSum.lequivCongrLeft R (Equiv.addRight (-k))).toLinearMap.comp
    (DirectSum.decomposeLinearEquiv 𝓜).toLinearMap

/-- Recombining the translated homogeneous components obtained from `shiftDecompose` recovers
the original element. -/
@[stacks 0FQ1 "shifted grading decomposition left inverse"]
theorem shiftDecompose_left_inv
    (𝓜 : ι → Submodule R M) [DirectSum.Decomposition 𝓜] (k : ι) :
    (DirectSum.coeLinearMap (shiftGrading 𝓜 k)).comp (shiftDecompose 𝓜 k) =
      LinearMap.id := sorry

/-- Decomposing an element recombined from translated homogeneous components recovers those
components. -/
@[stacks 0FQ1 "shifted grading decomposition right inverse"]
theorem shiftDecompose_right_inv
    (𝓜 : ι → Submodule R M) [DirectSum.Decomposition 𝓜] (k : ι) :
    (shiftDecompose 𝓜 k).comp (DirectSum.coeLinearMap (shiftGrading 𝓜 k)) =
      LinearMap.id := sorry

/-- Translation of an internal grading preserves its direct-sum decomposition. -/
@[reducible, stacks 0FQ1 "shifted grading internal decomposition"]
instance shiftDecomposition
    (𝓜 : ι → Submodule R M) [DirectSum.Decomposition 𝓜] (k : ι) :
    DirectSum.Decomposition (shiftGrading 𝓜 k) :=
  DirectSum.Decomposition.ofLinearMap (shiftGrading 𝓜 k) (shiftDecompose 𝓜 k)
    (shiftDecompose_left_inv 𝓜 k) (shiftDecompose_right_inv 𝓜 k)

end Grading

namespace Right

variable {ι : Type x} [DecidableEq ι] [AddCommGroup ι]
variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]
variable {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]

/-- The unchanged right action remains homogeneous after translating the module grading. -/
@[stacks 0FQ1 "homogeneity of the shifted right action"]
theorem shift_gradedSMul (M : Right.{x, y, v, u} 𝒜) (k : ι) :
    SetLike.GradedSMul (GradedModule.oppositeGrading 𝒜)
      (GradedModule.shiftGrading M.grading k) := sorry

/-- The grading shift of a right graded module. It keeps the carrier and right action and
reindexes the homogeneous pieces by `n ↦ n + k`. -/
@[stacks 0FQ1 "grading shift of a right graded module"]
def shift (M : Right.{x, y, v, u} 𝒜) (k : ι) : Right.{x, y, v, u} 𝒜 where
  carrier := M.carrier
  addCommGroup := M.addCommGroup
  moduleBase := M.moduleBase
  moduleOpposite := M.moduleOpposite
  isScalarTower := M.isScalarTower
  grading := GradedModule.shiftGrading M.grading k
  decomposition := GradedModule.shiftDecomposition M.grading k
  gradedSMul := shift_gradedSMul M k

/-- The grading of a shifted right module is the translated original grading. -/
@[simp]
theorem shift_grading (M : Right.{x, y, v, u} 𝒜) (k n : ι) :
    (M.shift k).grading n = M.grading (n + k) := sorry

/-- Membership in a shifted homogeneous piece is membership in the translated original piece. -/
@[simp]
theorem mem_shift_grading_iff (M : Right.{x, y, v, u} 𝒜) (k n : ι) {x : M} :
    x ∈ (M.shift k).grading n ↔ x ∈ M.grading (n + k) := sorry

/-- A right-module shift does not change the underlying right action. -/
@[simp]
theorem shift_action (M : Right.{x, y, v, u} 𝒜) (k : ι) (x : M) (a : A) :
    (M.shift k).action x a = M.action x a := sorry

/-- Shifting by zero recovers the original right graded module. -/
@[simp]
theorem shift_zero (M : Right.{x, y, v, u} 𝒜) : M.shift 0 = M := sorry

/-- Successive shifts add their translation degrees. -/
@[simp]
theorem shift_shift (M : Right.{x, y, v, u} 𝒜) (k l : ι) :
    (M.shift k).shift l = M.shift (k + l) := sorry

/-- The underlying map of a homogeneous morphism remains homogeneous after simultaneous
translation of source and target gradings. -/
@[stacks 0FQ1 "homogeneous maps under simultaneous grading shift"]
theorem HomogeneousMap.shift_mem {L M : Right.{x, y, v, u} 𝒜} {n : ι}
    (f : HomogeneousMap L M n) (k : ι) :
    f.1 ∈ HomogeneousMap (L.shift k) (M.shift k) n := sorry

/-- Simultaneously shifting the source and target preserves a homogeneous map and its degree. -/
def HomogeneousMap.shift {L M : Right.{x, y, v, u} 𝒜} {n : ι}
    (f : HomogeneousMap L M n) (k : ι) :
    HomogeneousMap (L.shift k) (M.shift k) n :=
  ⟨f.1, HomogeneousMap.shift_mem f k⟩

/-- A shifted homogeneous map has the same underlying right-linear map. -/
@[simp]
theorem HomogeneousMap.shift_apply {L M : Right.{x, y, v, u} 𝒜} {n : ι}
    (f : HomogeneousMap L M n) (k : ι) (x : L) :
    (HomogeneousMap.shift f k).1 x = f.1 x := sorry

/-- Simultaneous shift preserves addition of homogeneous maps. -/
@[stacks 0FQ1 "additivity of simultaneous shift on homogeneous maps"]
theorem HomogeneousMap.shift_add {L M : Right.{x, y, v, u} 𝒜} {n : ι}
    (f g : HomogeneousMap L M n) (k : ι) :
    HomogeneousMap.shift (f + g) k =
      HomogeneousMap.shift f k + HomogeneousMap.shift g k := sorry

/-- Simultaneous shift preserves base-ring scalar multiplication of homogeneous maps. -/
@[stacks 0FQ1 "linearity of simultaneous shift on homogeneous maps"]
theorem HomogeneousMap.shift_smul {L M : Right.{x, y, v, u} 𝒜} {n : ι}
    (r : R) (f : HomogeneousMap L M n) (k : ι) :
    HomogeneousMap.shift (r • f) k = r • HomogeneousMap.shift f k := sorry

/-- Simultaneous shift on one homogeneous summand, as a linear map. -/
@[stacks 0FQ1 "linear simultaneous shift on a homogeneous-map summand"]
def HomogeneousMap.shiftLinear (L M : Right.{x, y, v, u} 𝒜) (n k : ι) :
    HomogeneousMap L M n →ₗ[R] HomogeneousMap (L.shift k) (M.shift k) n where
  toFun f := HomogeneousMap.shift f k
  map_add' := fun f g ↦ HomogeneousMap.shift_add f g k
  map_smul' := fun r f ↦ HomogeneousMap.shift_smul r f k

/-- Simultaneous shift on the total graded Hom module. -/
def Hom.shiftLinear (L M : Right.{x, y, v, u} 𝒜) (k : ι) :
    Hom L M →ₗ[R] Hom (L.shift k) (M.shift k) :=
  DirectSum.toModule R ι (Hom (L.shift k) (M.shift k)) fun n ↦
    (Hom.of (L.shift k) (M.shift k) n).comp (HomogeneousMap.shiftLinear L M n k)

/-- Shift a morphism by simultaneously shifting its source and target. -/
def shiftMap {L M : Right.{x, y, v, u} 𝒜} (f : L ⟶ M) (k : ι) :
    L.shift k ⟶ M.shift k :=
  Hom.shiftLinear L M k f

/-- Shifting a homogeneous generator retains its homogeneous component. -/
@[simp]
theorem shiftMap_of (L M : Right.{x, y, v, u} 𝒜) (n k : ι)
    (f : HomogeneousMap L M n) :
    shiftMap (Hom.of L M n f) k =
      Hom.of (L.shift k) (M.shift k) n (HomogeneousMap.shift f k) := sorry

/-- Shifting preserves identity morphisms. -/
@[simp]
theorem shiftMap_id (M : Right.{x, y, v, u} 𝒜) (k : ι) :
    shiftMap (𝟙 M) k = 𝟙 (M.shift k) := sorry

/-- Shifting preserves composition of morphisms. -/
@[simp]
theorem shiftMap_comp {K L M : Right.{x, y, v, u} 𝒜} (f : K ⟶ L) (g : L ⟶ M)
    (k : ι) : shiftMap (f ≫ g) k = shiftMap f k ≫ shiftMap g k := sorry

/-- Simultaneous grading shift is an endofunctor of the graded-module category. -/
@[stacks 0FQ1 "simultaneous grading-shift endofunctor"]
def shiftFunctor (k : ι) : Right.{x, y, v, u} 𝒜 ⥤ Right.{x, y, v, u} 𝒜 where
  obj M := M.shift k
  map f := shiftMap f k
  map_id := fun M ↦ shiftMap_id M k
  map_comp := fun f g ↦ shiftMap_comp f g k

/-- The shift functor acts on objects by the explicit grading shift. -/
@[simp]
theorem shiftFunctor_obj (k : ι) (M : Right.{x, y, v, u} 𝒜) :
    (shiftFunctor k).obj M = M.shift k := sorry

/-- The shift functor acts on morphisms by simultaneous shift. -/
@[simp]
theorem shiftFunctor_map (k : ι) {L M : Right.{x, y, v, u} 𝒜} (f : L ⟶ M) :
    (shiftFunctor k).map f = shiftMap f k := sorry

/-- The grading-shift endofunctor is additive. -/
instance shiftFunctor_additive (k : ι) : (shiftFunctor (𝒜 := 𝒜) k).Additive := sorry

/-- The grading-shift endofunctor is `R`-linear. -/
instance shiftFunctor_linear (k : ι) : Functor.Linear R (shiftFunctor (𝒜 := 𝒜) k) := sorry

end Right

@[inherit_doc GradedModule.Right.shift]
scoped[RightGradedModule] notation:max M:max "[" k:max "]" =>
  GradedModule.Right.shift M k

end GradedModule

namespace GradedAlgebra

variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]

/-- The Koszul sign scalar on one homogeneous piece preserves addition. -/
@[stacks 0FQ1 "additivity of the Koszul sign on a homogeneous piece"]
theorem koszulSignPiece_add (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
    (k i : ℤ) (a b : 𝒜 i) :
    ((i * k).negOnePow : R) • (((a + b : 𝒜 i) : A)) =
      ((i * k).negOnePow : R) • (a : A) +
        ((i * k).negOnePow : R) • (b : A) := sorry

/-- The Koszul sign scalar on one homogeneous piece preserves base-ring scalar multiplication. -/
@[stacks 0FQ1 "linearity of the Koszul sign on a homogeneous piece"]
theorem koszulSignPiece_smul (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
    (k i : ℤ) (r : R) (a : 𝒜 i) :
    ((i * k).negOnePow : R) • (((r • a : 𝒜 i) : A)) =
      r • (((i * k).negOnePow : R) • (a : A)) := sorry

/-- Multiplication by the Koszul sign on one homogeneous component. -/
@[stacks 0FQ1 "Koszul sign on a homogeneous component"]
def koszulSignPiece (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
    (k i : ℤ) : 𝒜 i →ₗ[R] A where
  toFun a := ((i * k).negOnePow : R) • (a : A)
  map_add' := koszulSignPiece_add 𝒜 k i
  map_smul' := koszulSignPiece_smul 𝒜 k i

/-- The linear Koszul sign operator associated to an integer grading and a shift degree `k`.
On the degree-`i` piece it acts by the scalar `(-1)^(i * k)`. -/
@[stacks 0FQ1 "linear Koszul sign operator"]
def koszulSignLinear (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] (k : ℤ) : A →ₗ[R] A :=
  (DirectSum.toModule R ℤ A fun i ↦ koszulSignPiece 𝒜 k i).comp
    (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

/-- The linear Koszul sign operator is a left inverse to itself. -/
@[stacks 0FQ1 "left inverse law for the Koszul sign operator"]
theorem koszulSignLinear_leftInverse (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
    (k : ℤ) :
    Function.LeftInverse (koszulSignLinear 𝒜 k) (koszulSignLinear 𝒜 k) := sorry

/-- The linear Koszul sign operator is a right inverse to itself. -/
@[stacks 0FQ1 "right inverse law for the Koszul sign operator"]
theorem koszulSignLinear_rightInverse (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
    (k : ℤ) :
    Function.RightInverse (koszulSignLinear 𝒜 k) (koszulSignLinear 𝒜 k) := sorry

/-- The linear Koszul sign operator preserves multiplication. -/
@[stacks 0FQ1 "multiplicativity of the Koszul sign operator"]
theorem koszulSignLinear_map_mul (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
    (k : ℤ) (a b : A) :
    koszulSignLinear 𝒜 k (a * b) =
      koszulSignLinear 𝒜 k a * koszulSignLinear 𝒜 k b := sorry

/-- The linear Koszul sign operator preserves addition. -/
@[stacks 0FQ1 "additivity of the Koszul sign operator"]
theorem koszulSignLinear_map_add (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
    (k : ℤ) (a b : A) :
    koszulSignLinear 𝒜 k (a + b) =
      koszulSignLinear 𝒜 k a + koszulSignLinear 𝒜 k b := sorry

/-- The linear Koszul sign operator fixes the image of the base ring. -/
@[stacks 0FQ1 "base-ring compatibility of the Koszul sign operator"]
theorem koszulSignLinear_commutes (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
    (k : ℤ) (r : R) :
    koszulSignLinear 𝒜 k (algebraMap R A r) = algebraMap R A r := sorry

/-- The Koszul sign algebra automorphism associated to a shift degree `k`. -/
@[stacks 0FQ1 "Koszul sign algebra automorphism"]
def koszulSign (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] (k : ℤ) : A ≃ₐ[R] A where
  toFun := koszulSignLinear 𝒜 k
  invFun := koszulSignLinear 𝒜 k
  left_inv := koszulSignLinear_leftInverse 𝒜 k
  right_inv := koszulSignLinear_rightInverse 𝒜 k
  map_mul' := koszulSignLinear_map_mul 𝒜 k
  map_add' := koszulSignLinear_map_add 𝒜 k
  commutes' := koszulSignLinear_commutes 𝒜 k

/-- On a homogeneous element, the Koszul sign automorphism is multiplication by the expected
sign. -/
@[simp]
theorem koszulSign_apply_of_mem (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
    (k i : ℤ) {a : A} (ha : a ∈ 𝒜 i) :
    koszulSign 𝒜 k a = ((i * k).negOnePow : R) • a := sorry

/-- The Koszul sign automorphism for shift degree zero is the identity. -/
@[simp]
theorem koszulSign_zero (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] :
    koszulSign 𝒜 0 = AlgEquiv.refl := sorry

/-- Koszul sign automorphisms turn addition of shift degrees into composition. -/
theorem koszulSign_add (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] (k l : ℤ) :
    koszulSign 𝒜 (k + l) = (koszulSign 𝒜 k).trans (koszulSign 𝒜 l) := sorry

/-- Every Koszul sign automorphism is its own inverse. -/
@[simp]
theorem koszulSign_symm (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] (k : ℤ) :
    (koszulSign 𝒜 k).symm = koszulSign 𝒜 k := sorry

end GradedAlgebra

namespace GradedModule

namespace Left

variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]
variable {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]

/-- The left module structure pulled back along the Koszul sign automorphism. -/
@[reducible] def shiftModule (M : Left.{0, w, v, u} 𝒜) (k : ℤ) : Module A M :=
  Module.compHom M (GradedAlgebra.koszulSign 𝒜 k).toAlgHom.toRingHom

/-- Base scalars associate with the left action pulled back along the Koszul sign automorphism. -/
@[stacks 0FQ1 "scalar-tower law for the shifted left action"]
theorem shift_smul_assoc (M : Left.{0, w, v, u} 𝒜) (k : ℤ)
    (r : R) (a : A) (x : M) :
    @SMul.smul A M (M.shiftModule k).toSMul (r • a) x =
      r • (@SMul.smul A M (M.shiftModule k).toSMul a x) := sorry

/-- The Koszul-twisted left action remains homogeneous after translating the module grading. -/
@[stacks 0FQ1 "homogeneity of the shifted left action"]
theorem shift_smul_mem (M : Left.{0, w, v, u} 𝒜) (k : ℤ)
    {i j : ℤ} {a : A} {x : M} (ha : a ∈ 𝒜 i)
    (hx : x ∈ GradedModule.shiftGrading M.grading k j) :
    @SMul.smul A M (M.shiftModule k).toSMul a x ∈
      GradedModule.shiftGrading M.grading k (i + j) := sorry

/-- The scalar-tower proof object for the Koszul-twisted left module structure. -/
@[stacks 0FQ1 "scalar tower for the shifted left module"]
theorem shiftIsScalarTower (M : Left.{0, w, v, u} 𝒜) (k : ℤ) :
    @IsScalarTower R A M.carrier inferInstance (M.shiftModule k).toSMul
      M.moduleBase.toSMul := sorry

/-- The graded-action proof object for the Koszul-twisted left module structure. -/
@[stacks 0FQ1 "graded scalar action for the shifted left module"]
theorem shiftGradedSMul (M : Left.{0, w, v, u} 𝒜) (k : ℤ) :
    @SetLike.GradedSMul ℤ ℤ (Submodule R A) A (Submodule R M.carrier) M.carrier
      inferInstance inferInstance (M.shiftModule k).toSMul inferInstance
      𝒜 (GradedModule.shiftGrading M.grading k) := sorry

/-- The grading shift of a left graded module. It translates the grading and twists the action
by the Koszul sign automorphism. -/
@[stacks 0FQ1 "grading shift of a left graded module"]
def shift (M : Left.{0, w, v, u} 𝒜) (k : ℤ) : Left.{0, w, v, u} 𝒜 where
  carrier := M.carrier
  addCommMonoid := M.addCommMonoid
  moduleBase := M.moduleBase
  moduleAlgebra := M.shiftModule k
  isScalarTower := shiftIsScalarTower M k
  grading := GradedModule.shiftGrading M.grading k
  decomposition := GradedModule.shiftDecomposition M.grading k
  gradedSMul := shiftGradedSMul M k

/-- The grading of a shifted left module is the translated original grading. -/
@[simp]
theorem shift_grading (M : Left.{0, w, v, u} 𝒜) (k n : ℤ) :
    (M.shift k).grading n = M.grading (n + k) := sorry

/-- Membership in a shifted homogeneous piece is membership in the translated original piece. -/
@[simp]
theorem mem_shift_grading_iff (M : Left.{0, w, v, u} 𝒜) (k n : ℤ) {x : M} :
    x ∈ (M.shift k).grading n ↔ x ∈ M.grading (n + k) := sorry

/-- The shifted action is the original action pulled back along the Koszul sign automorphism. -/
@[simp]
theorem shift_action (M : Left.{0, w, v, u} 𝒜) (k : ℤ) (a : A) (x : M) :
    (a • x : M.shift k) = (GradedAlgebra.koszulSign 𝒜 k a) • x := sorry

/-- On a homogeneous algebra element, the shifted action is the Koszul-sign twist of the
original action. -/
@[simp]
theorem shift_action_of_mem (M : Left.{0, w, v, u} 𝒜) (k i : ℤ)
    {a : A} (ha : a ∈ 𝒜 i) (x : M) :
    (a • x : M.shift k) = ((i * k).negOnePow : R) • (a • x : M) := sorry

/-- Shifting a left graded module by zero recovers it. -/
@[simp]
theorem shift_zero (M : Left.{0, w, v, u} 𝒜) : M.shift 0 = M := sorry

/-- Successive left-module shifts add their translation degrees. -/
@[simp]
theorem shift_shift (M : Left.{0, w, v, u} 𝒜) (k l : ℤ) :
    (M.shift k).shift l = M.shift (k + l) := sorry

end Left

@[inherit_doc GradedModule.Left.shift]
scoped[LeftGradedModule] notation:max M:max "[" k:max "]" =>
  GradedModule.Left.shift M k

namespace Bimodule

variable {ι : Type x} [DecidableEq ι] [AddCommGroup ι]
variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]
variable {B : Type w} [Ring B] [Algebra R B]
variable {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]
variable {𝒝 : ι → Submodule R B} [GradedAlgebra 𝒝]

/-- Translating the grading preserves homogeneity of the unchanged left action. -/
@[stacks 0FQ1 "homogeneity of the left action under right shift"]
theorem rightShiftGradedSMulLeft
    (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) (k : ι) :
    SetLike.GradedSMul 𝒜 (GradedModule.shiftGrading M.grading k) := sorry

/-- The right shift of a graded bimodule keeps both actions and translates its grading. -/
@[stacks 0FQ1 "right shift of a graded bimodule"]
def rightShift (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) (k : ι) :
    Bimodule.{x, y, w, v, u} 𝒜 𝒝 where
  toRight := M.toRight.shift k
  moduleLeft := M.moduleLeft
  isScalarTowerLeft := M.isScalarTowerLeft
  smulCommClass := M.smulCommClass
  gradedSMulLeft := rightShiftGradedSMulLeft M k

/-- Forgetting the left action identifies a right-shifted bimodule with the shifted underlying
right module. -/
@[simp]
theorem rightShift_toRight (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) (k : ι) :
    (M.rightShift k).toRight = M.toRight.shift k := sorry

/-- The degree-`n` piece of the right shift is the original degree-`n + k` piece. -/
@[simp]
theorem rightShift_grading (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) (k n : ι) :
    (M.rightShift k).grading n = M.grading (n + k) := sorry

/-- The right shift does not change the left action. -/
@[simp]
theorem rightShift_leftAction (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝)
    (k : ι) (a : A) (x : M) :
    (M.rightShift k).leftAction a x = M.leftAction a x := sorry

/-- The right shift does not change the right action. -/
@[simp]
theorem rightShift_rightAction (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝)
    (k : ι) (x : M) (b : B) :
    (M.rightShift k).rightAction x b = M.rightAction x b := sorry

/-- Shifting a graded bimodule on the right by zero recovers it. -/
@[simp]
theorem rightShift_zero (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) : M.rightShift 0 = M := sorry

/-- Successive right shifts add their translation degrees. -/
@[simp]
theorem rightShift_add (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) (k l : ι) :
    (M.rightShift k).rightShift l = M.rightShift (k + l) := sorry

/-- The shifted underlying map still commutes with the unchanged left action. -/
@[stacks 0FQ1 "bimodule-map compatibility under right shift"]
theorem Hom.rightShift_mem {L M : Bimodule.{x, y, w, v, u} 𝒜 𝒝}
    (f : L ⟶ M) (k : ι) :
    Right.HomogeneousMap.shift (Hom.toRightHom f) k ∈
      homSubmodule (L.rightShift k) (M.rightShift k) := sorry

/-- Simultaneously right-shifting the source and target preserves a graded bimodule morphism. -/
def Hom.rightShift {L M : Bimodule.{x, y, w, v, u} 𝒜 𝒝} (f : L ⟶ M) (k : ι) :
    L.rightShift k ⟶ M.rightShift k :=
  ⟨Right.HomogeneousMap.shift (Hom.toRightHom f) k, Hom.rightShift_mem f k⟩

/-- A right-shifted bimodule morphism has the shifted underlying degree-zero right-module map. -/
@[simp]
theorem Hom.rightShift_toRightHom {L M : Bimodule.{x, y, w, v, u} 𝒜 𝒝}
    (f : L ⟶ M) (k : ι) :
    Hom.toRightHom (f.rightShift k) =
      Right.HomogeneousMap.shift (Hom.toRightHom f) k := sorry

/-- A right-shifted bimodule morphism has the same underlying function. -/
@[simp]
theorem Hom.rightShift_apply {L M : Bimodule.{x, y, w, v, u} 𝒜 𝒝}
    (f : L ⟶ M) (k : ι) (x : L) :
    Hom.toLinearMap (f.rightShift k) x = Hom.toLinearMap f x := sorry

/-- Shift a graded bimodule morphism by simultaneously right-shifting its source and target. -/
def rightShiftMap {L M : Bimodule.{x, y, w, v, u} 𝒜 𝒝} (f : L ⟶ M) (k : ι) :
    L.rightShift k ⟶ M.rightShift k :=
  f.rightShift k

/-- Right shift preserves identity morphisms. -/
@[simp]
theorem rightShiftMap_id (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) (k : ι) :
    rightShiftMap (𝟙 M) k = 𝟙 (M.rightShift k) := sorry

/-- Right shift preserves composition of morphisms. -/
@[simp]
theorem rightShiftMap_comp {K L M : Bimodule.{x, y, w, v, u} 𝒜 𝒝}
    (f : K ⟶ L) (g : L ⟶ M) (k : ι) :
    rightShiftMap (f ≫ g) k = rightShiftMap f k ≫ rightShiftMap g k := sorry

/-- Simultaneous right shift is an endofunctor of graded bimodules. -/
def rightShiftFunctor (k : ι) :
    Bimodule.{x, y, w, v, u} 𝒜 𝒝 ⥤ Bimodule.{x, y, w, v, u} 𝒜 𝒝 where
  obj M := M.rightShift k
  map f := rightShiftMap f k
  map_id := fun M ↦ rightShiftMap_id M k
  map_comp := fun f g ↦ rightShiftMap_comp f g k

/-- The right-shift functor acts on objects by the explicit right shift. -/
@[simp]
theorem rightShiftFunctor_obj (k : ι) (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) :
    (rightShiftFunctor (𝒜 := 𝒜) (𝒝 := 𝒝) k).obj M = M.rightShift k := sorry

/-- The right-shift functor acts on morphisms by simultaneous right shift. -/
@[simp]
theorem rightShiftFunctor_map (k : ι) {L M : Bimodule.{x, y, w, v, u} 𝒜 𝒝}
    (f : L ⟶ M) :
    (rightShiftFunctor (𝒜 := 𝒜) (𝒝 := 𝒝) k).map f = rightShiftMap f k := sorry

/-- The right-shift endofunctor is additive. -/
instance rightShiftFunctor_additive (k : ι) :
    (rightShiftFunctor (𝒜 := 𝒜) (𝒝 := 𝒝) k).Additive := sorry

/-- The right-shift endofunctor is `R`-linear. -/
instance rightShiftFunctor_linear (k : ι) :
    Functor.Linear R (rightShiftFunctor (𝒜 := 𝒜) (𝒝 := 𝒝) k) := sorry

end Bimodule

namespace Bimodule

variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]
variable {B : Type w} [Ring B] [Algebra R B]
variable {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]
variable {𝒝 : ℤ → Submodule R B} [GradedAlgebra 𝒝]

/-- The scalar tower for the Koszul-twisted left action on a left-shifted bimodule. -/
@[stacks 0FQ1 "scalar tower for left-shifted bimodules"]
theorem leftShiftIsScalarTower
    (M : Bimodule.{0, y, w, v, u} 𝒜 𝒝) (k : ℤ) :
    @IsScalarTower R A M.toRight.carrier inferInstance
      (M.toLeft.shiftModule k).toSMul M.toRight.moduleBase.toSMul := sorry

/-- The Koszul-twisted left action continues to commute with the unchanged right action. -/
@[stacks 0FQ1 "commuting actions for left-shifted bimodules"]
theorem leftShiftSMulCommClass
    (M : Bimodule.{0, y, w, v, u} 𝒜 𝒝) (k : ℤ) :
    @SMulCommClass A Bᵐᵒᵖ M.toRight.carrier
      (M.toLeft.shiftModule k).toSMul M.toRight.moduleOpposite.toSMul := sorry

/-- The Koszul-twisted left action is homogeneous for the translated grading. -/
@[stacks 0FQ1 "homogeneity of the left action under left shift"]
theorem leftShiftGradedSMulLeft
    (M : Bimodule.{0, y, w, v, u} 𝒜 𝒝) (k : ℤ) :
    @SetLike.GradedSMul ℤ ℤ (Submodule R A) A
      (Submodule R M.toRight.carrier) M.toRight.carrier
      inferInstance inferInstance (M.toLeft.shiftModule k).toSMul inferInstance
      𝒜 (GradedModule.shiftGrading M.grading k) := sorry

/-- The left shift of an integer-graded bimodule translates its grading and twists the left
action by the Koszul sign automorphism. -/
@[stacks 0FQ1 "left shift of a graded bimodule"]
def leftShift (M : Bimodule.{0, y, w, v, u} 𝒜 𝒝) (k : ℤ) :
    Bimodule.{0, y, w, v, u} 𝒜 𝒝 where
  toRight := M.toRight.shift k
  moduleLeft := M.toLeft.shiftModule k
  isScalarTowerLeft := leftShiftIsScalarTower M k
  smulCommClass := leftShiftSMulCommClass M k
  gradedSMulLeft := leftShiftGradedSMulLeft M k

/-- Forgetting the left action identifies a left-shifted bimodule with the shifted underlying
right module. -/
@[simp]
theorem leftShift_toRight (M : Bimodule.{0, y, w, v, u} 𝒜 𝒝) (k : ℤ) :
    (M.leftShift k).toRight = M.toRight.shift k := sorry

/-- Forgetting the right action identifies a left-shifted bimodule with the shift of its
underlying left graded module. -/
@[simp]
theorem leftShift_toLeft (M : Bimodule.{0, y, w, v, u} 𝒜 𝒝) (k : ℤ) :
    (M.leftShift k).toLeft = M.toLeft.shift k := sorry

/-- The degree-`n` piece of the left shift is the original degree-`n + k` piece. -/
@[simp]
theorem leftShift_grading (M : Bimodule.{0, y, w, v, u} 𝒜 𝒝) (k n : ℤ) :
    (M.leftShift k).grading n = M.grading (n + k) := sorry

/-- On a homogeneous algebra element, the shifted left action is the Koszul-sign twist of the
original action. -/
@[simp]
theorem leftShift_leftAction_of_mem (M : Bimodule.{0, y, w, v, u} 𝒜 𝒝)
    (k i : ℤ) {a : A} (ha : a ∈ 𝒜 i) (x : M) :
    (M.leftShift k).leftAction a x =
      ((i * k).negOnePow : R) • M.leftAction a x := sorry

/-- The left shift does not change the right action. -/
@[simp]
theorem leftShift_rightAction (M : Bimodule.{0, y, w, v, u} 𝒜 𝒝)
    (k : ℤ) (x : M) (b : B) :
    (M.leftShift k).rightAction x b = M.rightAction x b := sorry

/-- Shifting an integer-graded bimodule on the left by zero recovers it. -/
@[simp]
theorem leftShift_zero (M : Bimodule.{0, y, w, v, u} 𝒜 𝒝) : M.leftShift 0 = M := sorry

/-- Successive left shifts add their translation degrees. -/
@[simp]
theorem leftShift_add (M : Bimodule.{0, y, w, v, u} 𝒜 𝒝) (k l : ℤ) :
    (M.leftShift k).leftShift l = M.leftShift (k + l) := sorry

/-- The shifted underlying map remains compatible with the Koszul-twisted left actions. -/
@[stacks 0FQ1 "bimodule-map compatibility under left shift"]
theorem Hom.leftShift_mem {L M : Bimodule.{0, y, w, v, u} 𝒜 𝒝}
    (f : L ⟶ M) (k : ℤ) :
    Right.HomogeneousMap.shift (Hom.toRightHom f) k ∈
      homSubmodule (L.leftShift k) (M.leftShift k) := sorry

/-- Simultaneously left-shifting the source and target preserves a graded bimodule morphism. -/
def Hom.leftShift {L M : Bimodule.{0, y, w, v, u} 𝒜 𝒝} (f : L ⟶ M) (k : ℤ) :
    L.leftShift k ⟶ M.leftShift k :=
  ⟨Right.HomogeneousMap.shift (Hom.toRightHom f) k, Hom.leftShift_mem f k⟩

/-- A left-shifted bimodule morphism has the shifted underlying degree-zero right-module map. -/
@[simp]
theorem Hom.leftShift_toRightHom {L M : Bimodule.{0, y, w, v, u} 𝒜 𝒝}
    (f : L ⟶ M) (k : ℤ) :
    Hom.toRightHom (f.leftShift k) =
      Right.HomogeneousMap.shift (Hom.toRightHom f) k := sorry

/-- A left-shifted bimodule morphism has the same underlying function. -/
@[simp]
theorem Hom.leftShift_apply {L M : Bimodule.{0, y, w, v, u} 𝒜 𝒝}
    (f : L ⟶ M) (k : ℤ) (x : L) :
    Hom.toLinearMap (f.leftShift k) x = Hom.toLinearMap f x := sorry

/-- Shift a graded bimodule morphism by simultaneously left-shifting its source and target. -/
def leftShiftMap {L M : Bimodule.{0, y, w, v, u} 𝒜 𝒝} (f : L ⟶ M) (k : ℤ) :
    L.leftShift k ⟶ M.leftShift k :=
  f.leftShift k

/-- Left shift preserves identity morphisms. -/
@[simp]
theorem leftShiftMap_id (M : Bimodule.{0, y, w, v, u} 𝒜 𝒝) (k : ℤ) :
    leftShiftMap (𝟙 M) k = 𝟙 (M.leftShift k) := sorry

/-- Left shift preserves composition of morphisms. -/
@[simp]
theorem leftShiftMap_comp {K L M : Bimodule.{0, y, w, v, u} 𝒜 𝒝}
    (f : K ⟶ L) (g : L ⟶ M) (k : ℤ) :
    leftShiftMap (f ≫ g) k = leftShiftMap f k ≫ leftShiftMap g k := sorry

/-- Simultaneous left shift is an endofunctor of integer-graded bimodules. -/
def leftShiftFunctor (k : ℤ) :
    Bimodule.{0, y, w, v, u} 𝒜 𝒝 ⥤ Bimodule.{0, y, w, v, u} 𝒜 𝒝 where
  obj M := M.leftShift k
  map f := leftShiftMap f k
  map_id := fun M ↦ leftShiftMap_id M k
  map_comp := fun f g ↦ leftShiftMap_comp f g k

/-- The left-shift functor acts on objects by the explicit left shift. -/
@[simp]
theorem leftShiftFunctor_obj (k : ℤ) (M : Bimodule.{0, y, w, v, u} 𝒜 𝒝) :
    (leftShiftFunctor (𝒜 := 𝒜) (𝒝 := 𝒝) k).obj M = M.leftShift k := sorry

/-- The left-shift functor acts on morphisms by simultaneous left shift. -/
@[simp]
theorem leftShiftFunctor_map (k : ℤ) {L M : Bimodule.{0, y, w, v, u} 𝒜 𝒝}
    (f : L ⟶ M) :
    (leftShiftFunctor (𝒜 := 𝒜) (𝒝 := 𝒝) k).map f = leftShiftMap f k := sorry

/-- The left-shift endofunctor is additive. -/
instance leftShiftFunctor_additive (k : ℤ) :
    (leftShiftFunctor (𝒜 := 𝒜) (𝒝 := 𝒝) k).Additive := sorry

/-- The left-shift endofunctor is `R`-linear. -/
instance leftShiftFunctor_linear (k : ℤ) :
    Functor.Linear R (leftShiftFunctor (𝒜 := 𝒜) (𝒝 := 𝒝) k) := sorry

end Bimodule

@[inherit_doc GradedModule.Bimodule.rightShift]
scoped[GradedBimodule] notation:max M:max "[" k:max "]" =>
  GradedModule.Bimodule.rightShift M k

@[inherit_doc GradedModule.Bimodule.leftShift]
scoped[GradedBimodule] notation:max "[" k:max "]" M:max =>
  GradedModule.Bimodule.leftShift M k

end GradedModule
