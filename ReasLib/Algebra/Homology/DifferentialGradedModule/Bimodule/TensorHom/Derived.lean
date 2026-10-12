/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorHom
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Derived
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction
public import ReasLib.CategoryTheory.Adjunction.Linear
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived Tensor-Hom Adjunction for Differential Graded Bimodules

This leaf derives the concrete homotopy-category tensor-Hom adjunction.  Its public API is
indexed only by the DG bimodule; the localization presentations and pointwise-derived choices
remain implementation details.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory

universe u v w x

namespace DifferentialGradedBimodule.TensorHom

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, x} R}

/-- The total derived tensor and internal-Hom functors form the absolute-derived pair required
to derive their homotopy-category adjunction. -/
@[stacks 09LT "absolute derived tensor-Hom pair"]
instance derivedPair (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    Adjunction.TotalDerived.HasPair
      (G := (Tensor.dgFunctor N).mapK) (F := (internalHomDgFunctor N).mapK)
      (DifferentialGradedModule.quasiIso A) (DifferentialGradedModule.quasiIso B)
      (L1 := DifferentialGradedModule.Derived.Q A)
      (L2 := DifferentialGradedModule.Derived.Q B) := sorry

/-- Lemma 22.33.5 (09LT): derived tensoring by a DG bimodule is left adjoint to derived
fixed-source internal Hom. -/
@[stacks 09LT, stacks 0FTQ "derived tensor-Hom adjunction"]
noncomputable def derivedAdjunction (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    Tensor.derivedFunctor N ⊣ InternalHom.derivedFunctor N :=
  Adjunction.TotalDerived.HasPair.derived (homotopyAdjunction N)
    (DifferentialGradedModule.quasiIso A) (DifferentialGradedModule.quasiIso B)

namespace Derived

/-- Derived tensoring by a fixed DG bimodule is recognized as a left adjoint. -/
@[stacks 09LT "derived tensor functor is a left adjoint"]
instance tensorIsLeftAdjoint (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (Tensor.derivedFunctor N).IsLeftAdjoint := sorry

/-- Derived fixed-source internal Hom is recognized as a right adjoint. -/
@[stacks 09LT "derived internal Hom functor is a right adjoint"]
instance internalHomIsRightAdjoint (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (InternalHom.derivedFunctor N).IsRightAdjoint := sorry

end Derived

/-- The canonical shift comparisons on derived tensor and derived internal Hom are compatible
with the derived tensor-Hom adjunction. -/
@[stacks 09LT "shift-compatible derived tensor-Hom adjunction"]
instance derivedAdjunction_commShift (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (derivedAdjunction N).CommShift ℤ := sorry

/-- The derived tensor-Hom adjunction is an adjunction of triangulated categories. -/
@[stacks 09LT "triangulated derived tensor-Hom adjunction"]
instance derivedAdjunction_isTriangulated (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (derivedAdjunction N).IsTriangulated := sorry

/-- The concrete Hom equivalence of the derived tensor-Hom adjunction. -/
@[stacks 09LT "derived tensor-Hom equivalence",
  stacks 0FTQ "derived tensor-Hom equivalence"]
noncomputable def derivedHomEquiv (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    (P : DifferentialGradedModule.Derived.Category.{u, v} B) :
    ((Tensor.derivedFunctor N).obj M ⟶ P) ≃
      (M ⟶ (InternalHom.derivedFunctor N).obj P) :=
  (derivedAdjunction N).homEquiv M P

/-- The derived tensor-Hom equivalence as an `R`-linear equivalence. Its two functions are the
canonical currying and uncurrying maps of `derivedAdjunction`. -/
@[stacks 09LT "linear derived tensor-Hom equivalence",
  stacks 0FTQ "linear derived tensor-Hom equivalence"]
noncomputable def derivedHomLinearEquiv
    (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    (P : DifferentialGradedModule.Derived.Category.{u, v} B) :
    ((Tensor.derivedFunctor N).obj M ⟶ P) ≃ₗ[R]
      (M ⟶ (InternalHom.derivedFunctor N).obj P) :=
  (derivedAdjunction N).homLinearEquiv (k := R) M P

/-- The forward function of `derivedHomLinearEquiv` is derived currying. -/
@[simp, stacks 09LT "forward map of the linear derived tensor-Hom equivalence"]
theorem derivedHomLinearEquiv_apply
    (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    (P : DifferentialGradedModule.Derived.Category.{u, v} B)
    (f : (Tensor.derivedFunctor N).obj M ⟶ P) :
    derivedHomLinearEquiv N M P f = derivedHomEquiv N M P f := sorry

/-- The inverse function of `derivedHomLinearEquiv` is derived uncurrying. -/
@[simp, stacks 09LT "inverse map of the linear derived tensor-Hom equivalence"]
theorem derivedHomLinearEquiv_symm_apply
    (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    (P : DifferentialGradedModule.Derived.Category.{u, v} B)
    (f : M ⟶ (InternalHom.derivedFunctor N).obj P) :
    (derivedHomLinearEquiv N M P).symm f =
      (derivedHomEquiv N M P).symm f := sorry

/-- Naturality of derived tensor-Hom currying in the tensor input. -/
@[stacks 09LT "left naturality of derived tensor-Hom currying"]
theorem derivedHomEquiv_naturality_left
    (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M₁ M₂ : DifferentialGradedModule.Derived.Category.{u, v} A}
    {P : DifferentialGradedModule.Derived.Category.{u, v} B}
    (m : M₁ ⟶ M₂) (f : (Tensor.derivedFunctor N).obj M₂ ⟶ P) :
    derivedHomEquiv N M₁ P ((Tensor.derivedFunctor N).map m ≫ f) =
      m ≫ derivedHomEquiv N M₂ P f := sorry

/-- Naturality of the linear derived tensor-Hom equivalence in the tensor input. -/
@[stacks 09LT "left naturality of linear derived tensor-Hom currying"]
theorem derivedHomLinearEquiv_naturality_left
    (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M₁ M₂ : DifferentialGradedModule.Derived.Category.{u, v} A}
    {P : DifferentialGradedModule.Derived.Category.{u, v} B}
    (m : M₁ ⟶ M₂) (f : (Tensor.derivedFunctor N).obj M₂ ⟶ P) :
    derivedHomLinearEquiv N M₁ P ((Tensor.derivedFunctor N).map m ≫ f) =
      m ≫ derivedHomLinearEquiv N M₂ P f := sorry

/-- Naturality of the inverse derived tensor-Hom equivalence in the tensor input. -/
@[stacks 09LT "left naturality of inverse derived tensor-Hom currying"]
theorem derivedHomEquiv_symm_naturality_left
    (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M₁ M₂ : DifferentialGradedModule.Derived.Category.{u, v} A}
    {P : DifferentialGradedModule.Derived.Category.{u, v} B}
    (m : M₁ ⟶ M₂) (g : M₂ ⟶ (InternalHom.derivedFunctor N).obj P) :
    (derivedHomEquiv N M₁ P).symm (m ≫ g) =
      (Tensor.derivedFunctor N).map m ≫ (derivedHomEquiv N M₂ P).symm g := sorry

/-- Naturality of the inverse linear derived tensor-Hom equivalence in the tensor input. -/
@[stacks 09LT "left naturality of inverse linear derived tensor-Hom currying"]
theorem derivedHomLinearEquiv_symm_naturality_left
    (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M₁ M₂ : DifferentialGradedModule.Derived.Category.{u, v} A}
    {P : DifferentialGradedModule.Derived.Category.{u, v} B}
    (m : M₁ ⟶ M₂) (g : M₂ ⟶ (InternalHom.derivedFunctor N).obj P) :
    (derivedHomLinearEquiv N M₁ P).symm (m ≫ g) =
      (Tensor.derivedFunctor N).map m ≫ (derivedHomLinearEquiv N M₂ P).symm g := sorry

/-- Naturality of derived tensor-Hom currying in the internal-Hom input. -/
@[stacks 09LT "right naturality of derived tensor-Hom currying"]
theorem derivedHomEquiv_naturality_right
    (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M : DifferentialGradedModule.Derived.Category.{u, v} A}
    {P₁ P₂ : DifferentialGradedModule.Derived.Category.{u, v} B}
    (p : P₁ ⟶ P₂) (f : (Tensor.derivedFunctor N).obj M ⟶ P₁) :
    derivedHomEquiv N M P₂ (f ≫ p) =
      derivedHomEquiv N M P₁ f ≫ (InternalHom.derivedFunctor N).map p := sorry

/-- Naturality of the linear derived tensor-Hom equivalence in the target. -/
@[stacks 09LT "right naturality of linear derived tensor-Hom currying"]
theorem derivedHomLinearEquiv_naturality_right
    (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M : DifferentialGradedModule.Derived.Category.{u, v} A}
    {P₁ P₂ : DifferentialGradedModule.Derived.Category.{u, v} B}
    (p : P₁ ⟶ P₂) (f : (Tensor.derivedFunctor N).obj M ⟶ P₁) :
    derivedHomLinearEquiv N M P₂ (f ≫ p) =
      derivedHomLinearEquiv N M P₁ f ≫
        (InternalHom.derivedFunctor N).map p := sorry

/-- Naturality of the inverse derived tensor-Hom equivalence in the target. -/
@[stacks 09LT "right naturality of inverse derived tensor-Hom currying"]
theorem derivedHomEquiv_symm_naturality_right
    (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M : DifferentialGradedModule.Derived.Category.{u, v} A}
    {P₁ P₂ : DifferentialGradedModule.Derived.Category.{u, v} B}
    (p : P₁ ⟶ P₂) (g : M ⟶ (InternalHom.derivedFunctor N).obj P₁) :
    (derivedHomEquiv N M P₂).symm
        (g ≫ (InternalHom.derivedFunctor N).map p) =
      (derivedHomEquiv N M P₁).symm g ≫ p := sorry

/-- Naturality of the inverse linear derived tensor-Hom equivalence in the target. -/
@[stacks 09LT "right naturality of inverse linear derived tensor-Hom currying"]
theorem derivedHomLinearEquiv_symm_naturality_right
    (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M : DifferentialGradedModule.Derived.Category.{u, v} A}
    {P₁ P₂ : DifferentialGradedModule.Derived.Category.{u, v} B}
    (p : P₁ ⟶ P₂) (g : M ⟶ (InternalHom.derivedFunctor N).obj P₁) :
    (derivedHomLinearEquiv N M P₂).symm
        (g ≫ (InternalHom.derivedFunctor N).map p) =
      (derivedHomLinearEquiv N M P₁).symm g ≫ p := sorry

/-- Bifunctoriality of derived tensor-Hom currying when both the tensor input and the
internal-Hom target vary. -/
@[stacks 09LT "bifunctoriality of the derived tensor-Hom equivalence"]
theorem derivedHomEquiv_naturality
    (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M₁ M₂ : DifferentialGradedModule.Derived.Category.{u, v} A}
    {P₁ P₂ : DifferentialGradedModule.Derived.Category.{u, v} B}
    (m : M₁ ⟶ M₂) (f : (Tensor.derivedFunctor N).obj M₂ ⟶ P₁)
    (p : P₁ ⟶ P₂) :
    derivedHomEquiv N M₁ P₂ ((Tensor.derivedFunctor N).map m ≫ f ≫ p) =
      m ≫ derivedHomEquiv N M₂ P₁ f ≫ (InternalHom.derivedFunctor N).map p := sorry

section AdjointInstances

variable (N : DifferentialGradedBimodule.{u, v, w, x} A B)

#synth (Tensor.derivedFunctor N).IsLeftAdjoint
#synth (InternalHom.derivedFunctor N).IsRightAdjoint

end AdjointInstances

end DifferentialGradedBimodule.TensorHom
