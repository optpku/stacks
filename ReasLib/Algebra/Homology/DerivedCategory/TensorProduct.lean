/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.Algebra.Homology.HomotopyCategory.Monoidal
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Model
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Source
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Bifunctor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Monoidal
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Closed
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.KFlat
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.KFlat.Closed
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived tensor products of module complexes

The canonical construction is `DerivedTensor.Right.functor`. This file provides its
ring-indexed interface, comparison maps for chosen representatives, symmetry, and exactness.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory

section

variable {R : Type u} [CommRing R]

/-- A chosen homotopy-category representative of a derived `R`-complex. -/
@[stacks 064M "module derived representative"]
noncomputable abbrev tensorRightRepresentative
    (M : DerivedCategory (ModuleCat R)) : HomotopyCategory (ModuleCat R) (up ℤ) :=
  (HomotopyCategory.quotient (ModuleCat R) (up ℤ)).obj
    ((DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤
      DerivedCategory (ModuleCat R)).objPreimage M)

/-- The canonical isomorphism from the image of the chosen representative back to the original
derived object. -/
@[stacks 064M "module representative comparison"]
noncomputable def tensorRightRepresentativeIso (M : DerivedCategory (ModuleCat R)) :
    (DerivedCategory.Qh : HomotopyCategory (ModuleCat R) (up ℤ) ⥤
      DerivedCategory (ModuleCat R)).obj (tensorRightRepresentative M) ≅ M :=
  (DerivedCategory.quotientCompQhIso (ModuleCat R)).app
      ((DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤
        DerivedCategory (ModuleCat R)).objPreimage M) ≪≫
    ((DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤
      DerivedCategory (ModuleCat R)).objObjPreimageIso M)

/-- Tensoring on the right by a chosen representative on the homotopy category. -/
@[stacks 064M "module homotopy right tensor"]
noncomputable abbrev tensorRightFunctor (M : DerivedCategory (ModuleCat R)) :
    HomotopyCategory (ModuleCat R) (up ℤ) ⥤ HomotopyCategory (ModuleCat R) (up ℤ) :=
  MonoidalCategory.tensorRight (tensorRightRepresentative M)

/-- Homotopy-category tensoring by a chosen representative agrees with the canonical fixed-right
source functor. -/
@[stacks 064M "module fixed-right source comparison"]
noncomputable abbrev tensorRightFunctorSourceIso (M : DerivedCategory (ModuleCat R)) :
    tensorRightFunctor M ⋙
        (DerivedCategory.Qh : HomotopyCategory (ModuleCat R) (up ℤ) ⥤
          DerivedCategory (ModuleCat R)) ≅
      DerivedTensor.Right.sourceFunctor M :=
  DerivedTensor.Right.sourceFunctorIso M

/-- A K-flat/derived-tensor availability witness supplies the left-derived-functor instance needed
by the abstract construction.  Monoidality of the homotopy category alone is not sufficient. -/
@[stacks 064M "module right tensor derived instance"]
instance tensorRightFunctor_hasLeftDerivedFunctor (M : DerivedCategory (ModuleCat R))
    [DerivedTensor.Right.Has (C := ModuleCat R)] :
    (tensorRightFunctor M ⋙
      (DerivedCategory.Qh : HomotopyCategory (ModuleCat R) (up ℤ) ⥤
        DerivedCategory (ModuleCat R))).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)) := sorry
-- Proof strategy: transport `DerivedTensor.Right.Has.hasLeftDerivedFunctor` across
-- `tensorRightFunctorSourceIso M`, using invariance of left-derived-functor existence under a
-- natural isomorphism of the source functors.

/-- The canonical unbounded fixed-right derived tensor functor. -/
@[stacks 064M "derived tensor functor"]
noncomputable abbrev derivedTensorProduct (M : DerivedCategory (ModuleCat R)) :
    DerivedCategory (ModuleCat R) ⥤ DerivedCategory (ModuleCat R) :=
  DerivedTensor.Right.functor M

/-- The canonical fixed-right derived-tensor counit. -/
@[stacks 064M "module derived tensor counit"]
noncomputable abbrev derivedTensorProductCounit (M : DerivedCategory (ModuleCat R)) :
    (DerivedCategory.Qh : HomotopyCategory (ModuleCat R) (up ℤ) ⥤
        DerivedCategory (ModuleCat R)) ⋙
      derivedTensorProduct M ⟶ DerivedTensor.Right.sourceFunctor M :=
  DerivedTensor.Right.counit M

namespace DerivedTensorProduct

/-- The fixed-right derived tensor functor agrees with the fixed-right view of the canonical
two-variable derived tensor. -/
@[stacks 064M "module derived tensor bifunctor comparison"]
noncomputable abbrev bifunctorIso (M : DerivedCategory (ModuleCat R)) :
    derivedTensorProduct M ≅ DerivedTensor.Bifunctor.rightFunctor M :=
  DerivedTensor.Bifunctor.Right.iso M

/-- Objectwise comparison between the fixed-right and two-variable derived tensor products. -/
@[stacks 064M "module derived tensor object bifunctor comparison"]
noncomputable abbrev objIsoBifunctor (K M : DerivedCategory (ModuleCat R)) :
    (derivedTensorProduct M).obj K ≅ DerivedTensor.Bifunctor.obj K M :=
  DerivedTensor.Bifunctor.Right.isoApp M K

/-- Symmetry of the module derived tensor product. -/
@[stacks 0BYI, stacks 0FNQ "module derived tensor symmetry"]
noncomputable abbrev comm (K L : DerivedCategory (ModuleCat R)) :
    (derivedTensorProduct L).obj K ≅ (derivedTensorProduct K).obj L :=
  DerivedTensor.Bifunctor.Right.comm K L

end DerivedTensorProduct

/-- A namespace-level spelling of symmetry for the module derived tensor product. -/
@[stacks 0BYI "module derived tensor symmetry"]
noncomputable abbrev derivedTensorProduct_comm (K L : DerivedCategory (ModuleCat R)) :
    (derivedTensorProduct L).obj K ≅ (derivedTensorProduct K).obj L :=
  DerivedTensorProduct.comm K L

end

end CategoryTheory.DerivedCategory

namespace CategoryTheory

variable {R : Type u} [CommRing R]

/-- The canonical shift comparison on fixed-right derived tensoring. -/
@[stacks 064M "commutes with shift"]
noncomputable abbrev derivedTensorProduct_commShift
    (M : DerivedCategory (ModuleCat R)) :
    (DerivedCategory.derivedTensorProduct M).CommShift ℤ :=
  DerivedCategory.DerivedTensor.Right.commShift M

/-- The fixed-right derived tensor functor is exact in the triangulated sense. -/
@[stacks 064M "triangulated exactness"]
theorem derivedTensorProduct_isTriangulated (M : DerivedCategory (ModuleCat R)) :
    (DerivedCategory.derivedTensorProduct M).IsTriangulated := sorry
-- Proof strategy: unfold the abbreviation to `DerivedTensor.Right.functor M` and
-- apply the canonical fixed-right derived-tensor triangulatedness theorem supplied by the
-- K-flat model and its shift comparison.

/-- Module derived-tensor symmetry in the ambient category-theory namespace. -/
@[stacks 0BYI "module derived tensor symmetry namespace bridge"]
noncomputable abbrev derivedTensorProduct_comm
    (K L : DerivedCategory (ModuleCat R)) :
    (DerivedCategory.derivedTensorProduct L).obj K ≅
      (DerivedCategory.derivedTensorProduct K).obj L :=
  DerivedCategory.DerivedTensorProduct.comm K L

end CategoryTheory
