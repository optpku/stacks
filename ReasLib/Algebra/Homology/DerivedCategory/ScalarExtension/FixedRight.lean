/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Tensor
public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed-right scalar-extension tensor comparison

@stack 064M

The scalar-extension tensor comparison is naturally a two-variable statement.  This leaf owns
the fixed-right specialization needed by change-of-rings towers, while retaining the canonical
two-variable comparison as the data owner.  The ring parameters are aligned here with the current
`ModuleCat` facade; the underlying scalar-extension and derived-tensor APIs remain universe-aware.
The specialization is a 064M projection formula; the three-ring 08YU composition is a separate
consumer and should not be conflated with this single-ring component.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.DerivedExtension.Tensor.FixedRight

variable {R S : Type u} [CommRing R] [CommRing S]

local notation "DR" => DerivedCategory (ModuleCat R)

/-- The component of the fixed-right scalar-extension comparison at `X` and `N`. -/
@[stacks 064M "fixed-right scalar-extension tensor comparison component"]
noncomputable def comparisonIsoApp
    (σ : R →+* S) (N : DR) (X : DR) :
    (DerivedCategory.derivedTensorProduct N ⋙
        ModuleCat.derivedExtensionOfScalars σ).obj X ≅
      (ModuleCat.derivedExtensionOfScalars σ ⋙
        DerivedCategory.derivedTensorProduct
          ((ModuleCat.derivedExtensionOfScalars σ).obj N)).obj X :=
  (ModuleCat.derivedExtensionOfScalars σ).mapIso
      (DerivedCategory.DerivedTensorProduct.objIsoBifunctor X N) ≪≫
    (ModuleCat.DerivedExtension.Tensor.comparisonIso σ).app (X, N) ≪≫
    (DerivedCategory.DerivedTensorProduct.objIsoBifunctor
      ((ModuleCat.derivedExtensionOfScalars σ).obj X)
      ((ModuleCat.derivedExtensionOfScalars σ).obj N)).symm

/-- Naturality of the fixed-right scalar-extension tensor comparison. -/
@[reassoc, stacks 064M "naturality of fixed-right scalar-extension comparison"]
theorem comparisonIsoApp_naturality
    (σ : R →+* S) (N : DR) {X Y : DR} (f : X ⟶ Y) :
    let F := DerivedCategory.derivedTensorProduct N ⋙
      ModuleCat.derivedExtensionOfScalars σ
    let G := ModuleCat.derivedExtensionOfScalars σ ⋙
      DerivedCategory.derivedTensorProduct ((ModuleCat.derivedExtensionOfScalars σ).obj N)
    let eX : F.obj X ≅ G.obj X := comparisonIsoApp σ N X
    let eY : F.obj Y ≅ G.obj Y := comparisonIsoApp σ N Y
    F.map f ≫ eY.hom = eX.hom ≫ G.map f := sorry

/-- The fixed-right scalar-extension tensor comparison as a natural isomorphism of functors. -/
@[stacks 064M "fixed-right scalar-extension tensor comparison"]
noncomputable def comparisonIso
    (σ : R →+* S) (N : DR) :
    DerivedCategory.derivedTensorProduct N ⋙
        ModuleCat.derivedExtensionOfScalars σ ≅
      ModuleCat.derivedExtensionOfScalars σ ⋙
        DerivedCategory.derivedTensorProduct
          ((ModuleCat.derivedExtensionOfScalars σ).obj N) :=
  NatIso.ofComponents (comparisonIsoApp σ N)
    (comparisonIsoApp_naturality σ N)

/-- The named natural-isomorphism component is the fixed-right component defined above. -/
@[simp, stacks 064M "fixed-right scalar-extension comparison component formula"]
theorem comparisonIso_app
    (σ : R →+* S) (N : DR) (X : DR) :
    (comparisonIso σ N).app X = comparisonIsoApp σ N X := sorry

end CategoryTheory.ModuleCat.DerivedExtension.Tensor.FixedRight
