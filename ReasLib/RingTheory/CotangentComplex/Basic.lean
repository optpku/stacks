module

public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Construction
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# André-Quillen cotangent complexes of commutative ring maps

The algebra-level cotangent complex `L_{B/A}` of an object of `Under A`,
obtained from the standard polynomial resolution, the relative Kähler differentials of each
standard term, extension of scalars along the augmentation, and the alternating-face cochain
complex.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicTopology
open HomologicalComplex
open scoped Simplicial ZeroObject

noncomputable section

universe u

namespace CategoryTheory.CommRingCat.Under.CotangentComplex

/-- The degree-`n` algebra of the standard polynomial resolution of `B` over `A`. -/
abbrev standardTerm (A : CommRingCat.{u}) (B : Under A) (n : SimplexCategoryᵒᵖ) : Under A :=
  ((PolynomialResolution.evaluation A).obj B).left.obj n

/-- The augmentation map from a standard-resolution term to the resolved algebra. -/
abbrev standardAugmentation (A : CommRingCat.{u}) (B : Under A) (n : SimplexCategoryᵒᵖ) :
    (standardTerm A B n).right ⟶ B.right :=
  (((PolynomialResolution.evaluation A).obj B).hom.app n).right

/-- The morphism of standard-resolution terms induced by a simplex operator. -/
def standardMap (A : CommRingCat.{u}) (B : Under A) {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    standardTerm A B n ⟶ standardTerm A B m :=
  ((PolynomialResolution.evaluation A).obj B).left.map φ

/-- The standard-resolution augmentation is natural in the simplex category. -/
theorem standardMap_comp_augmentation (A : CommRingCat.{u}) (B : Under A)
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    (standardMap A B φ).right ≫ standardAugmentation A B m = standardAugmentation A B n :=
  sorry

/-- The ring-hom form of naturality of the standard-resolution augmentation. -/
theorem standardMap_comp_augmentation_hom (A : CommRingCat.{u}) (B : Under A)
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    (standardAugmentation A B n).hom =
      (standardAugmentation A B m).hom.comp (standardMap A B φ).right.hom :=
  sorry

/-- The map of relative Kähler differentials induced by a simplex operator. -/
def simplicialDifferentialsMap (A : CommRingCat.{u}) (B : Under A)
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    CommRingCat.KaehlerDifferential (standardTerm A B n).hom ⟶
      (ModuleCat.restrictScalars (standardMap A B φ).right.hom).obj
        (CommRingCat.KaehlerDifferential (standardTerm A B m).hom) :=
  CommRingCat.KaehlerDifferential.map
    ((Category.id_comp (standardTerm A B m).hom).trans (standardMap A B φ).w.symm)

/-- The map of `B`-modules induced by a simplicial operator of the polynomial resolution. -/
def simplicialModuleMap (A : CommRingCat.{u}) (B : Under A)
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    (ModuleCat.extendScalars (standardAugmentation A B n).hom).obj
        (CommRingCat.KaehlerDifferential (standardTerm A B n).hom) ⟶
      (ModuleCat.extendScalars (standardAugmentation A B m).hom).obj
        (CommRingCat.KaehlerDifferential (standardTerm A B m).hom) :=
  ((ModuleCat.extendRestrictScalarsAdj (standardAugmentation A B n).hom).homEquiv _ _).symm
    (simplicialDifferentialsMap A B φ ≫
      (ModuleCat.restrictScalars (standardMap A B φ).right.hom).map
        ((ModuleCat.extendRestrictScalarsAdj (standardAugmentation A B m).hom).unit.app _) ≫
      (ModuleCat.restrictScalarsComp' (standardMap A B φ).right.hom
          (standardAugmentation A B m).hom (standardAugmentation A B n).hom
          (standardMap_comp_augmentation_hom A B φ)).inv.app _)

/-- The identity simplicial operator acts as the identity on the associated module. -/
theorem simplicialModuleMap_id (A : CommRingCat.{u}) (B : Under A) (n : SimplexCategoryᵒᵖ) :
    simplicialModuleMap A B (𝟙 n) = 𝟙 _ :=
  sorry

/-- Simplicial-operator composition is preserved by the associated module maps. -/
theorem simplicialModuleMap_comp (A : CommRingCat.{u}) (B : Under A)
    {n m k : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (ψ : m ⟶ k) :
    simplicialModuleMap A B (φ ≫ ψ) = simplicialModuleMap A B φ ≫ simplicialModuleMap A B ψ :=
  sorry

/-- The simplicial `B`-module `Ω_{P_•/A} ⊗_{P_•} B` attached to the polynomial resolution. -/
def simplicialModule (A : CommRingCat.{u}) (B : Under A) :
    SimplicialObject (ModuleCat.{u} B.right) where
  obj n := (ModuleCat.extendScalars (standardAugmentation A B n).hom).obj
    (CommRingCat.KaehlerDifferential (standardTerm A B n).hom)
  map φ := simplicialModuleMap A B φ
  map_id n := simplicialModuleMap_id A B n
  map_comp φ ψ := simplicialModuleMap_comp A B φ ψ

/-- The degree-`n` term of the simplicial module is the base change of `Ω_{P_n/A}` along the
augmentation `P_n → B`. -/
theorem simplicialModule_obj (A : CommRingCat.{u}) (B : Under A) (n : SimplexCategoryᵒᵖ) :
    (simplicialModule A B).obj n =
      (ModuleCat.extendScalars (standardAugmentation A B n).hom).obj
        (CommRingCat.KaehlerDifferential (standardTerm A B n).hom) :=
  sorry

/-- The André-Quillen cotangent complex `L_{B/A}` of an object of `Under A`, as the
alternating-face cochain complex of the polynomial-resolution simplicial module. -/
def obj (A : CommRingCat.{u}) (B : Under A) : CochainComplex (ModuleCat.{u} B.right) ℤ :=
  ((alternatingFaceMapComplex (ModuleCat.{u} B.right)).obj (simplicialModule A B)).extend
    ComplexShape.embeddingDownNat

/-- The cohomological degree `-n` term of `L_{B/A}` is the `n`-th simplicial tensor term. -/
def objXIso (A : CommRingCat.{u}) (B : Under A) (n : ℕ) :
    (obj A B).X (-n) ≅ (simplicialModule A B).obj (op ⦋n⦌) :=
  extendXIso ((alternatingFaceMapComplex (ModuleCat.{u} B.right)).obj (simplicialModule A B))
    ComplexShape.embeddingDownNat (rfl : ComplexShape.embeddingDownNat.f n = -n)

/-- The cohomological degree `-n` component of `L_{B/A}` agrees with the simplicial tensor
term in degree `n`. -/
theorem obj_X (A : CommRingCat.{u}) (B : Under A) (n : ℕ) :
    (obj A B).X (-n) = (simplicialModule A B).obj (op ⦋n⦌) :=
  sorry

/-- `L_{B/A}` vanishes in strictly positive cohomological degrees. -/
theorem isZero_obj_X_of_pos (A : CommRingCat.{u}) (B : Under A) {n : ℤ} (hn : 0 < n) :
    IsZero ((obj A B).X n) :=
  sorry

end CategoryTheory.CommRingCat.Under.CotangentComplex

namespace RingHom

/-- The André-Quillen cotangent complex of a ring homomorphism, as a cochain complex of
modules over the codomain. -/
def cotangentComplex {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    CochainComplex (ModuleCat.{u} S) ℤ :=
  CommRingCat.Under.CotangentComplex.obj (CommRingCat.of R) (Under.mk (CommRingCat.ofHom f))

/-- Unfolding of the ring-hom cotangent complex as the cotangent complex of the corresponding
object of `Under`. -/
theorem cotangentComplex_eq {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    cotangentComplex f =
      CommRingCat.Under.CotangentComplex.obj (CommRingCat.of R)
        (Under.mk (CommRingCat.ofHom f)) :=
  sorry

end RingHom

namespace Algebra

/-- The André-Quillen cotangent complex of an algebra, as the cotangent complex of
`algebraMap R S`. -/
def cotangentComplex (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    CochainComplex (ModuleCat.{u} S) ℤ :=
  RingHom.cotangentComplex (algebraMap R S)

/-- Unfolding of the algebra-level cotangent complex as the cotangent complex of `algebraMap`. -/
theorem cotangentComplex_eq (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    cotangentComplex R S = RingHom.cotangentComplex (algebraMap R S) :=
  sorry

end Algebra
