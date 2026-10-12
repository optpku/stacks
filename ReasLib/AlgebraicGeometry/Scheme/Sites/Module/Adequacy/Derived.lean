/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.AffineEquivalence
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Characterization

@[expose] public section

open CategoryTheory CategoryTheory.Functor.RightDerived CategoryTheory.Limits
open AlgebraicGeometry Opposite

universe u

namespace SheafOfModules.AffineAdeq

/-- The category of modules on the big `τ`-site of `Spec A`, pinned at universe `u`. -/
abbrev ambientModuleCat (τ : StandardTopology) (A : CommRingCat.{u}) :=
  RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A)))

/-- The ambient module category of the big `τ`-site of `Spec A` is a normal mono category. -/
lemma ambient_isNormalMonoCategory (τ : StandardTopology) (A : CommRingCat.{u}) :
    IsNormalMonoCategory (ambientModuleCat τ A) := sorry

/-- The ambient module category of the big `τ`-site of `Spec A` is a normal epi category. -/
lemma ambient_isNormalEpiCategory (τ : StandardTopology) (A : CommRingCat.{u}) :
    IsNormalEpiCategory (ambientModuleCat τ A) := sorry

/-- The ambient module category of the big `τ`-site of `Spec A` has finite products. -/
lemma ambient_hasFiniteProducts (τ : StandardTopology) (A : CommRingCat.{u}) :
    HasFiniteProducts (ambientModuleCat τ A) := sorry

/-- The ambient module category of the big `τ`-site of `Spec A` has kernels. -/
lemma ambient_hasKernels (τ : StandardTopology) (A : CommRingCat.{u}) :
    HasKernels (ambientModuleCat τ A) := sorry

/-- The ambient module category of the big `τ`-site of `Spec A` has cokernels. -/
lemma ambient_hasCokernels (τ : StandardTopology) (A : CommRingCat.{u}) :
    HasCokernels (ambientModuleCat τ A) := sorry

/-- The category of modules on the big `τ`-site of `Spec A` is abelian. -/
noncomputable instance ambientAbelian (τ : StandardTopology) (A : CommRingCat.{u}) :
    Abelian (ambientModuleCat τ A) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := ambient_isNormalMonoCategory τ A
  toIsNormalEpiCategory := ambient_isNormalEpiCategory τ A
  has_finite_products := ambient_hasFiniteProducts τ A
  has_kernels := ambient_hasKernels τ A
  has_cokernels := ambient_hasCokernels τ A

/-- The right adjoint of the affine-adequate inclusion, as a functor on the
ambient module category of the big `τ`-site of `Spec A`. -/
noncomputable def coreflector (τ : StandardTopology) (A : CommRingCat.{u}) :
    ambientModuleCat τ A ⥤ AffineAdeq τ A :=
  (inclusion τ A).rightAdjoint

/-- The affine-adequate category on the big `τ`-site of `Spec A` is a normal mono category. -/
lemma affineAdeq_isNormalMonoCategory (τ : StandardTopology) (A : CommRingCat.{u}) :
    IsNormalMonoCategory (AffineAdeq τ A) := sorry

/-- The affine-adequate category on the big `τ`-site of `Spec A` is a normal epi category. -/
lemma affineAdeq_isNormalEpiCategory (τ : StandardTopology) (A : CommRingCat.{u}) :
    IsNormalEpiCategory (AffineAdeq τ A) := sorry

/-- The affine-adequate category on the big `τ`-site of `Spec A` has finite products. -/
lemma affineAdeq_hasFiniteProducts (τ : StandardTopology) (A : CommRingCat.{u}) :
    HasFiniteProducts (AffineAdeq τ A) := sorry

/-- The affine-adequate category on the big `τ`-site of `Spec A` has kernels. -/
lemma affineAdeq_hasKernels (τ : StandardTopology) (A : CommRingCat.{u}) :
    HasKernels (AffineAdeq τ A) := sorry

/-- The affine-adequate category on the big `τ`-site of `Spec A` has cokernels. -/
lemma affineAdeq_hasCokernels (τ : StandardTopology) (A : CommRingCat.{u}) :
    HasCokernels (AffineAdeq τ A) := sorry

/-- The affine-adequate category on the big `τ`-site of `Spec A` is abelian. -/
noncomputable instance affineAdeqAbelian (τ : StandardTopology) (A : CommRingCat.{u}) :
    Abelian (AffineAdeq τ A) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := affineAdeq_isNormalMonoCategory τ A
  toIsNormalEpiCategory := affineAdeq_isNormalEpiCategory τ A
  has_finite_products := affineAdeq_hasFiniteProducts τ A
  has_kernels := affineAdeq_hasKernels τ A
  has_cokernels := affineAdeq_hasCokernels τ A

/-- The affine-adequate coreflector is additive. -/
instance coreflectorAdditive (τ : StandardTopology) (A : CommRingCat.{u}) :
    (coreflector τ A).Additive := sorry

/-- Every positive-degree right-derived value of the affine-adequate coreflector
is zero on an affine-adequate module sheaf. -/
theorem coreflectorRightDerivedIsZero (τ : StandardTopology) (A : CommRingCat.{u})
    (ℱ : AffineAdeq τ A)
    [HasInjectiveResolutions (ambientModuleCat τ A)] (p : ℕ) (hp : 0 < p) :
    IsZero (((coreflector τ A).rightDerived p).obj ((inclusion τ A).obj ℱ)) := sorry

/-- The affine-adequate coreflector has vanishing positive-degree right-derived
values on every affine-adequate module sheaf. -/
theorem coreflectorVanishesAboveZero (τ : StandardTopology) (A : CommRingCat.{u})
    (ℱ : AffineAdeq τ A)
    [HasInjectiveResolutions (ambientModuleCat τ A)] :
    Vanishes.aboveZero (coreflector τ A) ((inclusion τ A).obj ℱ) := sorry

end SheafOfModules.AffineAdeq
