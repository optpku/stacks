module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.CupProduct
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Cohomology.AffineBase
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear
public import ReasLib.Topology.KrullDimension.Equidimensional
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape TopologicalSpace
open DerivedCategory.DerivedTensor.Right.Monoidal Functor.RightDerived.Homotopy
open scoped AlgebraicGeometry MonoidalCategory TensorProduct

noncomputable section

universe u


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
variable [derivedMonoidal : MonoidalCategory (coefficientDerived p)]
variable [qhMonoidal : Functor.Monoidal
  (DerivedCategory.Qh : HomotopyCategory (coefficientModules p) (up ℤ) ⥤
    coefficientDerived p)]
variable [globalLaxMonoidal : (globalDerivedFunctor p).LaxMonoidal]

/-- The complementary-degree cup product, with its target transported to degree `2 * d`. -/
noncomputable def cupToTopMorphism (d : ℕ) (i : ℤ) :
    cohomology p i ⊗ cohomology p (2 * (d : ℤ) - i) ⟶
      cohomology p (2 * (d : ℤ)) :=
  cohomologyCupProduct p i (2 * (d : ℤ) - i) ≫
    eqToHom (congrArg (cohomology p) (add_sub_cancel i (2 * (d : ℤ))))

/-- The underlying value of the complementary-degree cup product on two cohomology classes. -/
noncomputable def cupToTopValue (d : ℕ) (i : ℤ)
    (x : cohomologyOverAffineBase p i)
    (y : cohomologyOverAffineBase p (2 * (d : ℤ) - i)) :
    cohomologyOverAffineBase p (2 * (d : ℤ)) :=
  (cupToTopMorphism p d i).hom (x ⊗ₜ[coefficientRing p] y)

/-- The complementary-degree cup-product value is additive in its first argument. -/
theorem cupToTopValue_add_left (d : ℕ) (i : ℤ)
    (x x' : cohomologyOverAffineBase p i)
    (y : cohomologyOverAffineBase p (2 * (d : ℤ) - i)) :
    cupToTopValue p d i (x + x') y =
      cupToTopValue p d i x y + cupToTopValue p d i x' y := sorry

/-- The complementary-degree cup-product value is `k`-linear in its first argument. -/
theorem cupToTopValue_smul_left (d : ℕ) (i : ℤ)
    (a : k) (x : cohomologyOverAffineBase p i)
    (y : cohomologyOverAffineBase p (2 * (d : ℤ) - i)) :
    cupToTopValue p d i (a • x) y = a • cupToTopValue p d i x y := sorry

/-- The complementary-degree cup-product value is additive in its second argument. -/
theorem cupToTopValue_add_right (d : ℕ) (i : ℤ)
    (x : cohomologyOverAffineBase p i)
    (y y' : cohomologyOverAffineBase p (2 * (d : ℤ) - i)) :
    cupToTopValue p d i x (y + y') =
      cupToTopValue p d i x y + cupToTopValue p d i x y' := sorry

/-- The complementary-degree cup-product value is `k`-linear in its second argument. -/
theorem cupToTopValue_smul_right (d : ℕ) (i : ℤ)
    (a : k) (x : cohomologyOverAffineBase p i)
    (y : cohomologyOverAffineBase p (2 * (d : ℤ) - i)) :
    cupToTopValue p d i x (a • y) = a • cupToTopValue p d i x y := sorry

/-- The complementary-degree de Rham cup product as a curried `k`-linear map. -/
noncomputable def cupToTop (d : ℕ) (i : ℤ) :
    cohomologyOverAffineBase p i →ₗ[k]
      cohomologyOverAffineBase p (2 * (d : ℤ) - i) →ₗ[k]
        cohomologyOverAffineBase p (2 * (d : ℤ)) :=
  LinearMap.mk₂ k (cupToTopValue p d i)
    (cupToTopValue_add_left p d i) (cupToTopValue_smul_left p d i)
    (cupToTopValue_add_right p d i) (cupToTopValue_smul_right p d i)

/-- Applying `cupToTop` gives the cup product in complementary degrees. -/
theorem cupToTop_apply (d : ℕ) (i : ℤ)
    (x : cohomologyOverAffineBase p i)
    (y : cohomologyOverAffineBase p (2 * (d : ℤ) - i)) :
    cupToTop p d i x y = cupToTopValue p d i x y := sorry

/-- The cup-trace pairing attached to a top-degree de Rham trace. -/
noncomputable def pairing (d : ℕ)
    (t : cohomologyOverAffineBase p (2 * (d : ℤ)) ⟶ ModuleCat.of k k) (i : ℤ) :
    cohomologyOverAffineBase p i →ₗ[k]
      cohomologyOverAffineBase p (2 * (d : ℤ) - i) →ₗ[k] k :=
  (cupToTop p d i).compr₂ t.hom

/-- The cup-trace pairing sends `(x, y)` to the trace of their complementary-degree cup
product. -/
theorem pairing_apply (d : ℕ)
    (t : cohomologyOverAffineBase p (2 * (d : ℤ)) ⟶ ModuleCat.of k k) (i : ℤ)
    (x : cohomologyOverAffineBase p i)
    (y : cohomologyOverAffineBase p (2 * (d : ℤ) - i)) :
    pairing p d t i x y = t.hom (cupToTopValue p d i x y) := sorry

/-- A top-degree de Rham trace is perfect when all its complementary-degree cup-trace
pairings are perfect. -/
def IsPerfect (d : ℕ)
    (t : cohomologyOverAffineBase p (2 * (d : ℤ)) ⟶ ModuleCat.of k k) : Prop :=
  ∀ i : ℤ, (pairing p d t i).IsPerfPair

/-- Perfectness of a de Rham trace is exactly degreewise perfectness of its cup-trace
pairings. -/
theorem isPerfect_iff (d : ℕ)
    (t : cohomologyOverAffineBase p (2 * (d : ℤ)) ⟶ ModuleCat.of k k) :
    IsPerfect p d t ↔ ∀ i : ℤ, (pairing p d t i).IsPerfPair := sorry

/-- A perfect cup-trace pairing identifies degree-`i` de Rham cohomology with the dual of its
complementary degree. -/
noncomputable def dualityEquiv (d : ℕ)
    (t : cohomologyOverAffineBase p (2 * (d : ℤ)) ⟶ ModuleCat.of k k)
    (h : IsPerfect p d t) (i : ℤ) :
    cohomologyOverAffineBase p i ≃ₗ[k]
      Module.Dual k (cohomologyOverAffineBase p (2 * (d : ℤ) - i)) :=
  LinearEquiv.ofBijective (pairing p d t i) (h i).bijective_left

/-- The duality equivalence evaluates by the original cup-trace pairing. -/
theorem dualityEquiv_apply (d : ℕ)
    (t : cohomologyOverAffineBase p (2 * (d : ℤ)) ⟶ ModuleCat.of k k)
    (h : IsPerfect p d t) (i : ℤ) (x : cohomologyOverAffineBase p i) :
    dualityEquiv p d t h i x = pairing p d t i x := sorry

end AlgebraicGeometry.Scheme.DeRham.CohomologyTrace

namespace AlgebraicGeometry.Scheme.DeRham

variable {k : Type u} [Field k] (X : SchemeOverField k) (d : ℕ)
variable [Nonempty X.left] [Smooth X.hom] [IsProper X.hom]
variable [EquidimensionalSpace X.left]
variable [derivedMonoidal : MonoidalCategory (coefficientDerived X.hom)]
variable [qhMonoidal : Functor.Monoidal
  (DerivedCategory.Qh : HomotopyCategory (coefficientModules X.hom) (up ℤ) ⥤
    coefficientDerived X.hom)]
variable [globalLaxMonoidal : (globalDerivedFunctor X.hom).LaxMonoidal]

/-- A nonempty smooth proper equidimensional `k`-scheme of
dimension `d` admits a `k`-linear trace on `H^(2 * d)_dR(X / k)` whose cup-trace pairing
is perfect in every integer degree. -/
@[stacks 0FW7]
theorem existsDeRhamPoincareTrace
    (h_dimension : topologicalKrullDim X.left = d) :
    ∃ t : cohomologyOverAffineBase X.hom (2 * (d : ℤ)) ⟶ ModuleCat.of k k,
      CohomologyTrace.IsPerfect X.hom d t := sorry

/-- Any two perfect top-degree de Rham traces differ by
precomposition with multiplication by a unit of `Γ(X.left, ⊤)`. -/
@[stacks 0FW7]
theorem deRhamPoincareTrace_unique
    (h_dimension : topologicalKrullDim X.left = d)

    (t t' : cohomologyOverAffineBase X.hom (2 * (d : ℤ)) ⟶ ModuleCat.of k k)
    (ht : CohomologyTrace.IsPerfect X.hom d t)
    (ht' : CohomologyTrace.IsPerfect X.hom d t') :
    ∃ u : Γ(X.left, ⊤)ˣ,
      t' = CohomologyTrace.unitAction X.hom (2 * (d : ℤ)) u ≫ t := sorry

end AlgebraicGeometry.Scheme.DeRham
