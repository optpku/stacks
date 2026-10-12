/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap50.Lemma_50_20_2
public import stacks_project.Chap50.Lemma_50_3_4
public import stacks_project.Chap50.Lemma_50_4_1_CupProduct
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape TopologicalSpace
open DerivedCategory.DerivedTensor.Right.Monoidal Functor.RightDerived.Homotopy
open scoped AlgebraicGeometry MonoidalCategory TensorProduct

noncomputable section

universe u

-- Local instance justification (defeq pin): cup products use the standard derived-category presentation.
attribute [local instance] HasDerivedCategory.standard
-- Local instance justification (search instability): cup products require the canonical integer-graded tensor theorem.
attribute [local instance] SheafOfModules.RingedSite.IntGraded.hasTensor

namespace AlgebraicGeometry.Scheme.DeRham.CohomologyTrace

variable {k : Type u} [Field k]

/-- Multiplication by a global unit on the sheaf of relative differential `i`-forms. -/
noncomputable def hodgeFormUnitAction {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    (u : Γ(X, ⊤)ˣ) (i : ℕ) :
    RingedSpace.DeRham.form.{u} p.toLRSHom.toShHom i ⟶
      RingedSpace.DeRham.form.{u} p.toLRSHom.toShHom i :=
  RingedSpace.globalSectionMul.{u} (u : Γ(X, ⊤))
    (RingedSpace.DeRham.form.{u} p.toLRSHom.toShHom i)

/-- Multiplication by a global unit on the degree-`i` relative de Rham term, after restriction
from `𝒪_X`-modules to the coefficient sheaf pulled back from `Spec k`. -/
noncomputable def formUnitAction {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    (u : Γ(X, ⊤)ˣ) (i : ℕ) : (deRhamComplex p).X i ⟶ (deRhamComplex p).X i :=
  (SheafOfModules.RingedSite.DeRham.restriction
      (RingedSpace.DeRham.structureMap p.toShHom)).map
    (hodgeFormUnitAction p u i)

/-- Multiplication by a global unit commutes with the relative de Rham differential when every
global function on the smooth proper `k`-scheme has zero differential. -/
theorem formUnitAction_comm {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] [IsProper p] (u : Γ(X, ⊤)ˣ) (i j : ℕ) (hij : (up ℕ).Rel i j) :
    formUnitAction p u i ≫ (deRhamComplex p).d i j =
      (deRhamComplex p).d i j ≫ formUnitAction p u j := sorry

/-- The chain endomorphism of the relative de Rham complex given by multiplication by a global
unit. -/
noncomputable def complexUnitAction {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] [IsProper p] (u : Γ(X, ⊤)ˣ) : deRhamComplex p ⟶ deRhamComplex p :=
  HomologicalComplex.Hom.mk (formUnitAction p u) (formUnitAction_comm p u)

/-- The action of a global unit on relative de Rham cohomology over the coefficient ring. -/
noncomputable def cohomologyUnitAction {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [IsProper p]
    (u : Γ(X, ⊤)ˣ) (n : ℤ) : cohomology p n ⟶ cohomology p n :=
  (DerivedCategory.homologyFunctor (coefficientModules p) n).map
    ((globalDerivedFunctor p).map
      (HomologicalComplex.extendMap (complexUnitAction p u) embeddingUpNat))

/-- The `k`-linear action of a global unit on relative de Rham cohomology. -/
noncomputable def unitAction {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] [IsProper p] (n : ℤ) (u : Γ(X, ⊤)ˣ) :
    cohomologyOverAffineBase p n ⟶ cohomologyOverAffineBase p n :=
  (ModuleCat.restrictScalars (baseRingMapOfAffineTarget p).hom).map
    (cohomologyUnitAction p u n)

/-- The unit global section acts as the identity on relative de Rham cohomology. -/
theorem unitAction_one {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] [IsProper p] (n : ℤ) : unitAction p n (1 : Γ(X, ⊤)ˣ) = 𝟙 _ := sorry

variable {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
-- Local instance justification (defeq pin): cup products use this canonical coefficient-sheaf monoidal structure.
noncomputable local instance : MonoidalCategory
    (RingedSpace.DeRham.Modules p.toLRSHom.toShHom) :=
  SheafOfModules.RingedSite.moduleMonoidalCategory
    (RingedSpace.DeRham.coefficients p.toLRSHom.toShHom)

-- Local instance justification (defeq pin): cup products use this standard totalized cochain monoidal structure.
noncomputable local instance : MonoidalCategory
    (CochainComplex (RingedSpace.DeRham.Modules p.toLRSHom.toShHom) ℤ) :=
  HomologicalComplex.monoidalCategory _ (up ℤ)

variable [derivedMonoidal : MonoidalCategory (coefficientDerived p)]
variable [∀ G₁ G₂ : GradedObject ℤ (coefficientModules p), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (coefficientModules p),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (coefficientModules p),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (coefficientModules p),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [qhMonoidal : Functor.Monoidal
  (DerivedCategory.Qh : HomotopyCategory (coefficientModules p) (up ℤ) ⥤
    coefficientDerived p)]
variable [globalLaxMonoidal : (globalDerivedFunctor p).LaxMonoidal]

/-- Complementary de Rham degrees add to the top degree `2 * d`. -/
theorem add_complementary_degree (d : ℕ) (i : ℤ) :
    i + (2 * (d : ℤ) - i) = 2 * (d : ℤ) := sorry

/-- The complementary-degree cup product, with its target transported to degree `2 * d`. -/
noncomputable def cupToTopMorphism (T : CoefficientTensorModel p) (d : ℕ) (i : ℤ) :
    cohomology p i ⊗ cohomology p (2 * (d : ℤ) - i) ⟶
      cohomology p (2 * (d : ℤ)) :=
  @cohomologyCupProduct _ _ p derivedMonoidal qhMonoidal globalLaxMonoidal
      T i (2 * (d : ℤ) - i) ≫
    eqToHom (congrArg (cohomology p) (add_complementary_degree d i))

/-- The underlying value of the complementary-degree cup product on two cohomology classes. -/
noncomputable def cupToTopValue (T : CoefficientTensorModel p) (d : ℕ) (i : ℤ)
    (x : cohomologyOverAffineBase p i)
    (y : cohomologyOverAffineBase p (2 * (d : ℤ) - i)) :
    cohomologyOverAffineBase p (2 * (d : ℤ)) :=
  (cupToTopMorphism p T d i).hom (x ⊗ₜ[coefficientRing p] y)

/-- The complementary-degree cup-product value is additive in its first argument. -/
theorem cupToTopValue_add_left (T : CoefficientTensorModel p) (d : ℕ) (i : ℤ)
    (x x' : cohomologyOverAffineBase p i)
    (y : cohomologyOverAffineBase p (2 * (d : ℤ) - i)) :
    cupToTopValue p T d i (x + x') y =
      cupToTopValue p T d i x y + cupToTopValue p T d i x' y := sorry

/-- The complementary-degree cup-product value is `k`-linear in its first argument. -/
theorem cupToTopValue_smul_left (T : CoefficientTensorModel p) (d : ℕ) (i : ℤ)
    (a : k) (x : cohomologyOverAffineBase p i)
    (y : cohomologyOverAffineBase p (2 * (d : ℤ) - i)) :
    cupToTopValue p T d i (a • x) y = a • cupToTopValue p T d i x y := sorry

/-- The complementary-degree cup-product value is additive in its second argument. -/
theorem cupToTopValue_add_right (T : CoefficientTensorModel p) (d : ℕ) (i : ℤ)
    (x : cohomologyOverAffineBase p i)
    (y y' : cohomologyOverAffineBase p (2 * (d : ℤ) - i)) :
    cupToTopValue p T d i x (y + y') =
      cupToTopValue p T d i x y + cupToTopValue p T d i x y' := sorry

/-- The complementary-degree cup-product value is `k`-linear in its second argument. -/
theorem cupToTopValue_smul_right (T : CoefficientTensorModel p) (d : ℕ) (i : ℤ)
    (a : k) (x : cohomologyOverAffineBase p i)
    (y : cohomologyOverAffineBase p (2 * (d : ℤ) - i)) :
    cupToTopValue p T d i x (a • y) = a • cupToTopValue p T d i x y := sorry

/-- The complementary-degree de Rham cup product as a curried `k`-linear map. -/
noncomputable def cupToTop (T : CoefficientTensorModel p) (d : ℕ) (i : ℤ) :
    cohomologyOverAffineBase p i →ₗ[k]
      cohomologyOverAffineBase p (2 * (d : ℤ) - i) →ₗ[k]
        cohomologyOverAffineBase p (2 * (d : ℤ)) :=
  LinearMap.mk₂ k (cupToTopValue p T d i)
    (cupToTopValue_add_left p T d i) (cupToTopValue_smul_left p T d i)
    (cupToTopValue_add_right p T d i) (cupToTopValue_smul_right p T d i)

/-- Applying `cupToTop` gives the tensor-model cup product in complementary degrees. -/
theorem cupToTop_apply (T : CoefficientTensorModel p) (d : ℕ) (i : ℤ)
    (x : cohomologyOverAffineBase p i)
    (y : cohomologyOverAffineBase p (2 * (d : ℤ) - i)) :
    cupToTop p T d i x y = cupToTopValue p T d i x y := sorry

/-- The cup-trace pairing attached to a top-degree de Rham trace. -/
noncomputable def pairing (T : CoefficientTensorModel p) (d : ℕ)
    (t : cohomologyOverAffineBase p (2 * (d : ℤ)) ⟶ ModuleCat.of k k) (i : ℤ) :
    cohomologyOverAffineBase p i →ₗ[k]
      cohomologyOverAffineBase p (2 * (d : ℤ) - i) →ₗ[k] k :=
  (cupToTop p T d i).compr₂ t.hom

/-- The cup-trace pairing sends `(x, y)` to the trace of their complementary-degree cup
product. -/
theorem pairing_apply (T : CoefficientTensorModel p) (d : ℕ)
    (t : cohomologyOverAffineBase p (2 * (d : ℤ)) ⟶ ModuleCat.of k k) (i : ℤ)
    (x : cohomologyOverAffineBase p i)
    (y : cohomologyOverAffineBase p (2 * (d : ℤ) - i)) :
    pairing p T d t i x y = t.hom (cupToTopValue p T d i x y) := sorry

/-- A top-degree de Rham trace is perfect when all its complementary-degree cup-trace
pairings are perfect. -/
def IsPerfect (T : CoefficientTensorModel p) (d : ℕ)
    (t : cohomologyOverAffineBase p (2 * (d : ℤ)) ⟶ ModuleCat.of k k) : Prop :=
  ∀ i : ℤ, (pairing p T d t i).IsPerfPair

/-- Perfectness of a de Rham trace is exactly degreewise perfectness of its cup-trace
pairings. -/
theorem isPerfect_iff (T : CoefficientTensorModel p) (d : ℕ)
    (t : cohomologyOverAffineBase p (2 * (d : ℤ)) ⟶ ModuleCat.of k k) :
    IsPerfect p T d t ↔ ∀ i : ℤ, (pairing p T d t i).IsPerfPair := sorry

/-- Cup-trace pairings are independent of the chosen coefficient tensor model. -/
theorem pairing_eq_of_models (T T' : CoefficientTensorModel p) (d : ℕ)
    (t : cohomologyOverAffineBase p (2 * (d : ℤ)) ⟶ ModuleCat.of k k) (i : ℤ) :
    pairing p T d t i = pairing p T' d t i := sorry

/-- Perfectness of a trace is independent of the chosen coefficient tensor model. -/
theorem isPerfect_congrModel (T T' : CoefficientTensorModel p) (d : ℕ)
    (t : cohomologyOverAffineBase p (2 * (d : ℤ)) ⟶ ModuleCat.of k k) :
    IsPerfect p T d t ↔ IsPerfect p T' d t := sorry

/-- A perfect cup-trace pairing identifies degree-`i` de Rham cohomology with the dual of its
complementary degree. -/
noncomputable def dualityEquiv (T : CoefficientTensorModel p) (d : ℕ)
    (t : cohomologyOverAffineBase p (2 * (d : ℤ)) ⟶ ModuleCat.of k k)
    (h : IsPerfect p T d t) (i : ℤ) :
    cohomologyOverAffineBase p i ≃ₗ[k]
      Module.Dual k (cohomologyOverAffineBase p (2 * (d : ℤ) - i)) :=
  LinearEquiv.ofBijective (pairing p T d t i) (h i).bijective_left

/-- The duality equivalence evaluates by the original cup-trace pairing. -/
theorem dualityEquiv_apply (T : CoefficientTensorModel p) (d : ℕ)
    (t : cohomologyOverAffineBase p (2 * (d : ℤ)) ⟶ ModuleCat.of k k)
    (h : IsPerfect p T d t) (i : ℤ) (x : cohomologyOverAffineBase p i) :
    dualityEquiv p T d t h i x = pairing p T d t i x := sorry

end AlgebraicGeometry.Scheme.DeRham.CohomologyTrace
