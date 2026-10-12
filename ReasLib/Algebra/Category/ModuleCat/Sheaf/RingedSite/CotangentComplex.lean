/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.CategoryTheory.Adjunction.SimplicialResolution.Construction
public import ReasLib.CategoryTheory.Sites.AlgebraicSheaf.FreeAlgebra
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cotangent complexes of morphisms of commutative ring sheaves

This module owns the standard free-algebra resolution of a commutative algebra sheaf and the
associated complex of module sheaves `L_{B/A}`.  Geometric specializations to morphisms of
ringed topoi, spaces, and schemes consume this owner rather than rebuilding the resolution.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicTopology
open HomologicalComplex
open SheafOfModules.RingedSite
open scoped Simplicial ZeroObject

noncomputable section

universe u

namespace SheafOfModules.RingedSite.CotangentComplex

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]

/-- The free-forgetful adjunction for commutative algebra sheaves under a fixed ring sheaf. -/
def freeForgetAdjunction (A : Sheaf J CommRingCat.{u}) :
    Sheaf.composeAndSheafify J CommRingCat.free ⋙ Under.costar A ⊣
      Under.forget A ⋙ sheafCompose J (CategoryTheory.forget CommRingCat.{u}) :=
  (Sheaf.adjunction J CommRingCat.adj).comp (Under.costarAdjForget A)

/-- The standard simplicial resolution of a commutative algebra sheaf, obtained by evaluating
the free-forgetful comonad. -/
def standardResolution (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    SimplicialObject.Augmented (Under A) :=
  (Adjunction.SimplicialResolution.eval (freeForgetAdjunction A)).obj B

/-- Degree zero of the standard resolution is the canonical polynomial presentation `A[B]`. -/
theorem standardResolution_obj_zero (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    (standardResolution A B).left.obj (op ⦋0⦌) =
      CategoryTheory.Sheaf.FreeAlgebra.Presentation.obj A B := sorry

/-- The degree-`n` algebra of the standard resolution of `B` over `A`. -/
abbrev standardTerm (A : Sheaf J CommRingCat.{u}) (B : Under A)
    (n : SimplexCategoryᵒᵖ) : Under A :=
  (standardResolution A B).left.obj n

/-- The augmentation map from a standard-resolution term to the resolved algebra sheaf. -/
abbrev standardAugmentation (A : Sheaf J CommRingCat.{u}) (B : Under A)
    (n : SimplexCategoryᵒᵖ) :
    (standardTerm A B n).right ⟶ B.right :=
  ((standardResolution A B).hom.app n).right

/-- The morphism of standard-resolution terms induced by a simplex operator. -/
def standardMap (A : Sheaf J CommRingCat.{u}) (B : Under A)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    standardTerm A B n ⟶ standardTerm A B m :=
  (standardResolution A B).left.map f

/-- The map of relative differentials induced by a simplex operator of the standard
resolution. -/
def simplicialDifferentialsMap (A : Sheaf J CommRingCat.{u}) (B : Under A)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    relativeDifferentials (standardTerm A B n).hom ⟶
      (restrictionAlong (standardMap A B f).right).obj
        (relativeDifferentials (standardTerm A B m).hom) :=
  RelativeDifferentials.map
    ⟨(Category.id_comp (standardTerm A B m).hom).trans (standardMap A B f).w.symm⟩

/-- The standard-resolution augmentation is natural in the simplex category. -/
theorem standardMap_comp_augmentation (A : Sheaf J CommRingCat.{u}) (B : Under A)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (standardMap A B f).right ≫ standardAugmentation A B m =
      standardAugmentation A B n := sorry

/-- Forgetting commutativity identifies the two successive restriction paths of a simplex
operator. -/
theorem standardMap_comp_augmentation_ringSheaf
    (A : Sheaf J CommRingCat.{u}) (B : Under A)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    ringSheafMap (standardAugmentation A B n) =
      ringSheafMap (standardMap A B f).right ≫
        ringSheafMap (standardAugmentation A B m) := sorry

/-- The differentials of a standard-resolution term extended to the resolved algebra. -/
def standardModuleTerm (A : Sheaf J CommRingCat.{u}) (B : Under A)
    (n : SimplexCategoryᵒᵖ) : SheafOfModules (ringSheaf J B.right) :=
  (ChangeOfRings.extendScalars (ringSheafMap (standardAugmentation A B n))).obj
    (relativeDifferentials (standardTerm A B n).hom)

/-- The map of `B`-modules induced by a simplicial operator of the standard resolution. -/
def simplicialModuleMap (A : Sheaf J CommRingCat.{u}) (B : Under A)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    standardModuleTerm A B n ⟶ standardModuleTerm A B m :=
  ((ChangeOfRings.extendRestrictAdjunction
      (ringSheafMap (standardAugmentation A B n))).homEquiv _ _).symm
    (simplicialDifferentialsMap A B f ≫
      (restrictionAlong (standardMap A B f).right).map
        ((ChangeOfRings.extendRestrictAdjunction
          (ringSheafMap (standardAugmentation A B m))).unit.app _) ≫
      (SheafOfModules.Restriction.compIso'
          (ringSheafMap (standardMap A B f).right) (ringSheafMap (standardAugmentation A B m))
          (ringSheafMap (standardAugmentation A B n))
          (standardMap_comp_augmentation_ringSheaf A B f)).hom.app _)

/-- The identity simplicial operator acts as the identity on the associated module. -/
theorem simplicialModuleMap_id (A : Sheaf J CommRingCat.{u}) (B : Under A)
    (n : SimplexCategoryᵒᵖ) :
    simplicialModuleMap A B (𝟙 n) = 𝟙 _ := sorry

/-- Simplicial-operator composition is preserved by the associated module maps. -/
theorem simplicialModuleMap_comp (A : Sheaf J CommRingCat.{u}) (B : Under A)
    {n m k : SimplexCategoryᵒᵖ} (f : n ⟶ m) (g : m ⟶ k) :
    simplicialModuleMap A B (f ≫ g) =
      simplicialModuleMap A B f ≫ simplicialModuleMap A B g := sorry

/-- The simplicial `B`-module `Ω_{P_•/A} ⊗_{P_•} B` attached to the standard resolution. -/
def simplicialModule (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    SimplicialObject (SheafOfModules (ringSheaf J B.right)) where
  obj n := standardModuleTerm A B n
  map f := simplicialModuleMap A B f
  map_id n := simplicialModuleMap_id A B n
  map_comp f g := simplicialModuleMap_comp A B f g

/-- Identifying the augmentation point of the standard resolution with the resolved algebra. -/
theorem standardResolution_right (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    (standardResolution A B).right = B := sorry

/-- The cotangent complex `L_{B/A}` of a morphism of commutative ring sheaves, as the
alternating-face cochain complex of the standard-resolution simplicial module. -/
def obj (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    CochainComplex (SheafOfModules (ringSheaf J B.right)) ℤ :=
  ((alternatingFaceMapComplex (SheafOfModules (ringSheaf J B.right))).obj
      (simplicialModule A B)).extend ComplexShape.embeddingDownNat

/-- Reusable notation for the cotangent complex of a morphism of commutative ring sheaves. -/
scoped[SheafOfModules.RingedSite.CotangentComplex] notation:max "L(" φ ")" =>
  SheafOfModules.RingedSite.CotangentComplex.obj _ (Under.mk φ)

/-- The cohomological degree `-n` term of `L_{B/A}` is the `n`-th simplicial tensor term. -/
def objXIso (A : Sheaf J CommRingCat.{u}) (B : Under A) (n : ℕ) :
    (obj A B).X (-n) ≅ (simplicialModule A B).obj (op ⦋n⦌) :=
  extendXIso
    ((alternatingFaceMapComplex (SheafOfModules (ringSheaf J B.right))).obj
      (simplicialModule A B))
    ComplexShape.embeddingDownNat (rfl : ComplexShape.embeddingDownNat.f n = -n)

/-- The cohomological degree `-n` component of `L_{B/A}` agrees with the simplicial tensor
term in degree `n`. -/
theorem obj_X (A : Sheaf J CommRingCat.{u}) (B : Under A) (n : ℕ) :
    (obj A B).X (-n) = (simplicialModule A B).obj (op ⦋n⦌) := sorry

/-- `L_{B/A}` vanishes in strictly positive cohomological degrees. -/
theorem isZero_obj_X_of_pos (A : Sheaf J CommRingCat.{u}) (B : Under A)
    {n : ℤ} (hn : 0 < n) : IsZero ((obj A B).X n) := sorry

end SheafOfModules.RingedSite.CotangentComplex
