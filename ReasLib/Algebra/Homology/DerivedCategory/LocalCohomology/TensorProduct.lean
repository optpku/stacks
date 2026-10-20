/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Cech
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Bifunctor.Map

/-!
# Local cohomology and derived tensor products

This module records the compatibility of local cohomology with derived tensor products
(Stacks 0ALY) and closure of ideal-power-torsion cohomology under derived tensor products.

For a right adjoint `RΓ` of the inclusion of derived modules with `I`-power-torsion cohomology,
the comparison maps are the canonical ones: tensor the counit of the adjunction with the identity
(or with another counit), and lift the resulting map through the adjunction, which is possible
because the source already has `I`-power-torsion cohomology.  Their invertibility is the content
of the lemma; the isomorphisms are `asIso` of these named canonical maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Right

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology

variable {A : Type u} [CommRing A]

/-- If either factor has ideal-power-torsion cohomology, then their derived tensor product
also has ideal-power-torsion cohomology. -/
theorem tensor_mem (I : Ideal A) (hI : I.FG)
    (K L : DerivedCategory (ModuleCat A))
    (hKL : cohomologyIn (ModuleCat.isIdealPowerTorsion I) K ∨
      cohomologyIn (ModuleCat.isIdealPowerTorsion I) L) :
    cohomologyIn (ModuleCat.isIdealPowerTorsion I)
      (DerivedTensor.Right.obj K L) := sorry

variable (I : Ideal A) (hI : I.FG)
  (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
  (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ)

/-- The canonical comparison `K ⊗ᴸ RΓ_Z(L) ⟶ RΓ_Z(K ⊗ᴸ L)`: the map `𝟙 ⊗ ε_L` to `K ⊗ᴸ L`,
lifted through the adjunction since its source has `I`-power-torsion cohomology. -/
noncomputable def tensorComparisonRight (K L : DerivedCategory (ModuleCat A)) :
    DerivedTensor.Right.obj K (RΓ.obj L).obj ⟶ (RΓ.obj (DerivedTensor.Right.obj K L)).obj :=
  (hRΓ.homEquiv
    (⟨DerivedTensor.Right.obj K (RΓ.obj L).obj,
      tensor_mem I hI K _ (Or.inr (RΓ.obj L).property)⟩ : IdealPowerTorsion I)
    (DerivedTensor.Right.obj K L)
    (tensorHom (𝟙 K) (hRΓ.counit.app L))).hom

/-- The right comparison followed by the counit is `𝟙 ⊗ ε_L`. -/
theorem tensorComparisonRight_comp_counit (K L : DerivedCategory (ModuleCat A)) :
    tensorComparisonRight I hI RΓ hRΓ K L ≫
        (hRΓ.counit.app (DerivedTensor.Right.obj K L)) =
      tensorHom (𝟙 K) (hRΓ.counit.app L) := sorry

/-- Lemma 47.9.5 (0ALY): the right comparison is invertible. -/
instance tensorComparisonRight_isIso (K L : DerivedCategory (ModuleCat A)) :
    IsIso (tensorComparisonRight I hI RΓ hRΓ K L) := sorry

/-- The canonical comparison `RΓ_Z(K) ⊗ᴸ L ⟶ RΓ_Z(K ⊗ᴸ L)`: the map `ε_K ⊗ 𝟙` to `K ⊗ᴸ L`,
lifted through the adjunction since its source has `I`-power-torsion cohomology. -/
noncomputable def tensorComparisonLeft (K L : DerivedCategory (ModuleCat A)) :
    DerivedTensor.Right.obj (RΓ.obj K).obj L ⟶ (RΓ.obj (DerivedTensor.Right.obj K L)).obj :=
  (hRΓ.homEquiv
    (⟨DerivedTensor.Right.obj (RΓ.obj K).obj L,
      tensor_mem I hI _ L (Or.inl (RΓ.obj K).property)⟩ : IdealPowerTorsion I)
    (DerivedTensor.Right.obj K L)
    (tensorHom (hRΓ.counit.app K) (𝟙 L))).hom

/-- The left comparison followed by the counit is `ε_K ⊗ 𝟙`. -/
theorem tensorComparisonLeft_comp_counit (K L : DerivedCategory (ModuleCat A)) :
    tensorComparisonLeft I hI RΓ hRΓ K L ≫
        (hRΓ.counit.app (DerivedTensor.Right.obj K L)) =
      tensorHom (hRΓ.counit.app K) (𝟙 L) := sorry

/-- Lemma 47.9.5 (0ALY): the left comparison is invertible. -/
instance tensorComparisonLeft_isIso (K L : DerivedCategory (ModuleCat A)) :
    IsIso (tensorComparisonLeft I hI RΓ hRΓ K L) := sorry

/-- The canonical comparison `RΓ_Z(K) ⊗ᴸ RΓ_Z(L) ⟶ RΓ_Z(K ⊗ᴸ L)`: the map `ε_K ⊗ ε_L` to
`K ⊗ᴸ L`, lifted through the adjunction. -/
noncomputable def tensorComparisonBoth (K L : DerivedCategory (ModuleCat A)) :
    DerivedTensor.Right.obj (RΓ.obj K).obj (RΓ.obj L).obj ⟶
      (RΓ.obj (DerivedTensor.Right.obj K L)).obj :=
  (hRΓ.homEquiv
    (⟨DerivedTensor.Right.obj (RΓ.obj K).obj (RΓ.obj L).obj,
      tensor_mem I hI _ _ (Or.inl (RΓ.obj K).property)⟩ : IdealPowerTorsion I)
    (DerivedTensor.Right.obj K L)
    (tensorHom (hRΓ.counit.app K) (hRΓ.counit.app L))).hom

/-- The two-sided comparison followed by the counit is `ε_K ⊗ ε_L`. -/
theorem tensorComparisonBoth_comp_counit (K L : DerivedCategory (ModuleCat A)) :
    tensorComparisonBoth I hI RΓ hRΓ K L ≫
        (hRΓ.counit.app (DerivedTensor.Right.obj K L)) =
      tensorHom (hRΓ.counit.app K) (hRΓ.counit.app L) := sorry

/-- Lemma 47.9.5 (0ALY): the two-sided comparison is invertible. -/
instance tensorComparisonBoth_isIso (K L : DerivedCategory (ModuleCat A)) :
    IsIso (tensorComparisonBoth I hI RΓ hRΓ K L) := sorry

/-- Lemma 47.9.5 (0ALY): `RΓ_Z(K ⊗ᴸ L) ≅ K ⊗ᴸ RΓ_Z(L)`, the inverse of the canonical
comparison `tensorComparisonRight`. -/
noncomputable def tensorObjIsoRight (K L : DerivedCategory (ModuleCat A)) :
    (RΓ.obj (DerivedTensor.Right.obj K L)).obj ≅
      DerivedTensor.Right.obj K (RΓ.obj L).obj :=
  (asIso (tensorComparisonRight I hI RΓ hRΓ K L)).symm

/-- Lemma 47.9.5 (0ALY): `RΓ_Z(K ⊗ᴸ L) ≅ RΓ_Z(K) ⊗ᴸ L`, the inverse of the canonical
comparison `tensorComparisonLeft`. -/
noncomputable def tensorObjIsoLeft (K L : DerivedCategory (ModuleCat A)) :
    (RΓ.obj (DerivedTensor.Right.obj K L)).obj ≅
      DerivedTensor.Right.obj (RΓ.obj K).obj L :=
  (asIso (tensorComparisonLeft I hI RΓ hRΓ K L)).symm

/-- Lemma 47.9.5 (0ALY): `RΓ_Z(K ⊗ᴸ L) ≅ RΓ_Z(K) ⊗ᴸ RΓ_Z(L)`, the inverse of the canonical
comparison `tensorComparisonBoth`. -/
noncomputable def tensorObjIsoBoth (K L : DerivedCategory (ModuleCat A)) :
    (RΓ.obj (DerivedTensor.Right.obj K L)).obj ≅
      DerivedTensor.Right.obj (RΓ.obj K).obj (RΓ.obj L).obj :=
  (asIso (tensorComparisonBoth I hI RΓ hRΓ K L)).symm

/-- The inverse of `tensorObjIsoRight` is the canonical right comparison. -/
@[simp]
theorem tensorObjIsoRight_inv (K L : DerivedCategory (ModuleCat A)) :
    (tensorObjIsoRight I hI RΓ hRΓ K L).inv = tensorComparisonRight I hI RΓ hRΓ K L := sorry

/-- The inverse of `tensorObjIsoLeft` is the canonical left comparison. -/
@[simp]
theorem tensorObjIsoLeft_inv (K L : DerivedCategory (ModuleCat A)) :
    (tensorObjIsoLeft I hI RΓ hRΓ K L).inv = tensorComparisonLeft I hI RΓ hRΓ K L := sorry

/-- The inverse of `tensorObjIsoBoth` is the canonical two-sided comparison. -/
@[simp]
theorem tensorObjIsoBoth_inv (K L : DerivedCategory (ModuleCat A)) :
    (tensorObjIsoBoth I hI RΓ hRΓ K L).inv = tensorComparisonBoth I hI RΓ hRΓ K L := sorry

end CategoryTheory.DerivedCategory.LocalCohomology
