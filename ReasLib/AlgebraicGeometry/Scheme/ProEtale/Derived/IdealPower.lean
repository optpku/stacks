module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.IdealPower
public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.Derived.Basic

/-!
# Ideal-power derived reductions and their degree-zero sections

The inverse system `n ↦ K ⊗ᴸ underline(Λ / I ^ n)` has canonical quotient
transitions. Constancy of derived module sheaves is essential-image membership
for the derived constant-sheaf functor. Degree-zero homology and sections
give the corresponding inverse system of modules.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

variable {Λ : Type w} [CommRing Λ]
variable {X : Scheme.{u}}
variable [HasWeakSheafify (topology X) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf (topology X) (ModuleCat.{w} Λ))]
variable [HasDerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))]
variable [MonoidalCategory (Sheaf (topology X) (ModuleCat.{w} Λ))]

-- Local declaration justification (instance diamond): module sheaves inherit
-- `HasZeroMorphisms` and `Preadditive` through `FullSubcategory`, whereas derived
-- tensor and exact derived functors use `Abelian.toPreadditive`. Suppress the
-- two embedding instances only while elaborating the affected declarations.
-- Parameter blocks restore both instances before any public declaration; each
-- declaration below uses its own scoped suppression.
attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory
variable [MonoidalPreadditive (Sheaf (topology X) (ModuleCat.{w} Λ))]
variable [∀ (K L : CochainComplex (Sheaf (topology X) (ModuleCat.{w} Λ)) ℤ),
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (Sheaf (topology X) (ModuleCat.{w} Λ))) (ComplexShape.up ℤ)]
variable [DerivedCategory.DerivedTensor.Right.Has
  (C := Sheaf (topology X) (ModuleCat.{w} Λ))]
variable [DerivedCategory.DerivedTensor.Left.Has
  (C := Sheaf (topology X) (ModuleCat.{w} Λ))]

attribute [instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory

attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory in
/-- The degree-zero complex of the constant sheaf of `Λ / I ^ n`. -/
def idealPowerSingle (I : Ideal Λ) (n : ℕ) :
    DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ)) :=
  (DerivedCategory.singleFunctor (Sheaf (topology X) (ModuleCat.{w} Λ)) (0 : ℤ)).obj
    ((constantIdealPowerQuotientSheafSystem (topology X) I).obj (op n))

attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory in
/-- `idealPowerSingle` is the degree-zero embedding of `underline(Λ / I ^ n)`. -/
theorem idealPowerSingle_obj (I : Ideal Λ) (n : ℕ) :
    idealPowerSingle I n =
      (DerivedCategory.singleFunctor (Sheaf (topology X) (ModuleCat.{w} Λ)) (0 : ℤ)).obj
        ((constantIdealPowerQuotientSheafSystem (topology X) I).obj (op n)) := sorry

attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory in
/-- The successor map of constant ideal-power sheaves, induced by `Ideal.Quotient.factor`. -/
def idealPowerQuotientSheafStep (I : Ideal Λ) (n : ℕ) :
    (constantIdealPowerQuotientSheafSystem (topology X) I).obj (op (n + 1)) ⟶
      (constantIdealPowerQuotientSheafSystem (topology X) I).obj (op n) :=
  (constantIdealPowerQuotientSheafSystem (topology X) I).map (homOfLE (Nat.le_succ n)).op

attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory in
/-- The sheaf successor is the constant sheaf of the module quotient transition. -/
theorem idealPowerQuotientSheafStep_eq (I : Ideal Λ) (n : ℕ) :
    idealPowerQuotientSheafStep I n =
      (constantSheaf (topology X) (ModuleCat.{w} Λ)).map
        (idealPowerQuotientTransition I n) := sorry

attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory in
/-- The derived successor on degree-zero constant ideal-power complexes. -/
def idealPowerSingleStep (I : Ideal Λ) (n : ℕ) :
    (idealPowerSingle I (n + 1) :
      DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) ⟶
      (idealPowerSingle I n :
        DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) :=
  (DerivedCategory.singleFunctor (Sheaf (topology X) (ModuleCat.{w} Λ)) (0 : ℤ)).map
    (idealPowerQuotientSheafStep I n)

attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory in
/-- `idealPowerSingleStep` is `singleFunctor` applied to the sheaf successor. -/
theorem idealPowerSingleStep_eq (I : Ideal Λ) (n : ℕ) :
    idealPowerSingleStep I n =
      (DerivedCategory.singleFunctor (Sheaf (topology X) (ModuleCat.{w} Λ)) (0 : ℤ)).map
        (idealPowerQuotientSheafStep I n) := sorry

attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory in
/-- The derived reduction `K ⊗ᴸ underline(Λ / I ^ n)` in `D(X_proétale, Λ)`, as the
fixed-left derived tensor of `K` with `idealPowerSingle I n`. -/
def idealPowerTensor (I : Ideal Λ)
    (K : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) (n : ℕ) :
    DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ)) :=
  DerivedCategory.DerivedTensor.Left.obj K (idealPowerSingle I n)

attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory in
/-- The inverse system of derived reductions `n ↦ K ⊗ᴸ underline(Λ / I ^ n)`. -/
def idealPowerTensorSystem (I : Ideal Λ)
    (K : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) :
    SequentialInverseSystem
      (DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) :=
  Functor.ofOpSequence (idealPowerSingleStep I) ⋙
    DerivedCategory.DerivedTensor.Left.functor K

attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory in
/-- The successor transition of derived reductions, induced by `Ideal.Quotient.factor`. -/
def idealPowerTensorStep (I : Ideal Λ)
    (K : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) (n : ℕ) :
    (idealPowerTensorSystem I K).obj (op (n + 1)) ⟶
      (idealPowerTensorSystem I K).obj (op n) :=
  (idealPowerTensorSystem I K).map (homOfLE (Nat.le_succ n)).op

attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory in
/-- Evaluating the reduction inverse system at stage `n` recovers `idealPowerTensor`. -/
theorem idealPowerTensorSystem_obj (I : Ideal Λ)
    (K : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) (n : ℕ) :
    (idealPowerTensorSystem I K).obj (op n) = idealPowerTensor I K n := sorry

attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory in
/-- The successor map of the reduction system is `idealPowerTensorStep`. -/
theorem idealPowerTensorSystem_map_succ (I : Ideal Λ)
    (K : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) (n : ℕ) :
    (idealPowerTensorSystem I K).map (homOfLE (Nat.le_succ n)).op =
      idealPowerTensorStep I K n := sorry

attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory
variable [(constantSheaf (topology X) (ModuleCat.{w} Λ)).Additive]
variable [PreservesFiniteLimits (constantSheaf (topology X) (ModuleCat.{w} Λ))]
variable [PreservesFiniteColimits (constantSheaf (topology X) (ModuleCat.{w} Λ))]

attribute [instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory

attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory in
/-- A derived sheaf of `Λ`-modules is a complex of constant sheaves when it lies in the
essential image of `constantSheaf.mapDerivedCategory`. -/
def IsConstantComplex
    (L : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) : Prop :=
  (constantSheaf (topology X) (ModuleCat.{w} Λ)).mapDerivedCategory.essImage L

attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory in
/-- `IsConstantComplex` is essential-image membership for the derived constant-sheaf functor. -/
theorem isConstantComplex_iff
    (L : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) :
    IsConstantComplex L ↔
      (constantSheaf (topology X) (ModuleCat.{w} Λ)).mapDerivedCategory.essImage L := sorry

attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory in
/-- A derived object isomorphic to the derived constant sheaf of a complex of modules is a
constant complex. -/
theorem isConstantComplex_of_iso
    {E : DerivedCategory (ModuleCat.{w} Λ)}
    {L : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))}
    (e : (constantSheaf (topology X) (ModuleCat.{w} Λ)).mapDerivedCategory.obj E ≅ L) :
    IsConstantComplex L := sorry

attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory in
/-- The inverse system of degree-zero homology sheaves of the derived reductions. -/
def homologySheafSystem (I : Ideal Λ)
    (K : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) :
    SequentialInverseSystem (Sheaf (topology X) (ModuleCat.{w} Λ)) :=
  idealPowerTensorSystem I K ⋙
    DerivedCategory.homologyFunctor (Sheaf (topology X) (ModuleCat.{w} Λ)) (0 : ℤ)

attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory in
/-- The degree-zero homology sheaf of the `n`th derived reduction. -/
theorem homologySheafSystem_obj (I : Ideal Λ)
    (K : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) (n : ℕ) :
    (homologySheafSystem I K).obj (op n) =
      (DerivedCategory.homologyFunctor
          (Sheaf (topology X) (ModuleCat.{w} Λ)) (0 : ℤ)).obj
        (idealPowerTensor I K n) := sorry

attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory in
/-- The inverse system `n ↦ H^0(X, K ⊗ᴸ Λ / I ^ n)` of `Λ`-modules, realized as
sections of the degree-zero homology sheaves over `X`. -/
def degreeZeroSectionsSystem (I : Ideal Λ)
    (K : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) :
    SequentialInverseSystem (ModuleCat.{w} Λ) :=
  homologySheafSystem I K ⋙
    (sheafSections (topology X) (ModuleCat.{w} Λ)).obj (op (ProEt.mk (𝟙 X)))

attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory in
/-- Evaluating the degree-zero sections system is sections of the corresponding
homology sheaf over `X`. -/
theorem degreeZeroSectionsSystem_obj (I : Ideal Λ)
    (K : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))) (n : ℕ) :
    (degreeZeroSectionsSystem I K).obj (op n) =
      ((sheafSections (topology X) (ModuleCat.{w} Λ)).obj (op (ProEt.mk (𝟙 X)))).obj
        ((homologySheafSystem I K).obj (op n)) := sorry

end AlgebraicGeometry.Scheme.ProEt

end
