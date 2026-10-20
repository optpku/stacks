/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.CategoryTheory.Shift.Induced
public import ReasLib.Algebra.Category.DifferentialGraded.Homotopy.FunctorCategory
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy

/-!
# Categorical Shifts of Differential Graded Modules

This leaf promotes the explicit integer shift of right differential graded modules to coherent
shift functors.  It then transports those shifts to closed degree-zero morphisms and to the DG
homotopy category.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedModule.Shift

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra R}

/-- Shifting by a fixed integer is an endofunctor on right differential graded modules. -/
def functor (A : CochainDGAlgebra R) (k : ℤ) :
    DifferentialGradedModule.{u, v} A ⥤ DifferentialGradedModule.{u, v} A where
  obj M := M[k]
  map f := shiftMap f k
  map_id := sorry
  map_comp := sorry

/-- The shift functor uses the explicit shifted module on objects. -/
@[simp] theorem functor_obj (A : CochainDGAlgebra R)
    (M : DifferentialGradedModule.{u, v} A) (k : ℤ) :
    (functor.{u, v} A k).obj M = M[k] := sorry

/-- The shift functor uses the degreewise shifted map on morphisms. -/
@[simp] theorem functor_map (A : CochainDGAlgebra R)
    {M N : DifferentialGradedModule.{u, v} A} (f : M ⟶ N) (k : ℤ) :
    (functor.{u, v} A k).map f = shiftMap f k := sorry

/-- The component identifying the zero shift with the original differential graded module. -/
def zeroApp (M : DifferentialGradedModule.{u, v} A) : M[0] ≅ M where
  hom :=
    { hom := fun n ↦ ModuleCat.castLinearMap (congrArg M.X (add_zero n)) LinearMap.id
      comm_d := sorry
      comm_smul := sorry }
  inv :=
    { hom := fun n ↦ ModuleCat.castLinearMap (congrArg M.X (add_zero n).symm) LinearMap.id
      comm_d := sorry
      comm_smul := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward zero-shift comparison is degreewise transport along `n + 0 = n`. -/
@[simp] theorem zeroApp_hom_hom (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (zeroApp M).hom.hom n =
      ModuleCat.castLinearMap (congrArg M.X (add_zero n)) LinearMap.id := sorry

/-- The inverse zero-shift comparison is degreewise transport along `n = n + 0`. -/
@[simp] theorem zeroApp_inv_hom (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (zeroApp M).inv.hom n =
      ModuleCat.castLinearMap (congrArg M.X (add_zero n).symm) LinearMap.id := sorry

/-- The zero-shift comparison is natural in the differential graded module. -/
def zero (A : CochainDGAlgebra R) :
    functor.{u, v} A 0 ≅ Functor.id (DifferentialGradedModule.{u, v} A) :=
  NatIso.ofComponents zeroApp (fun _ ↦ sorry)

/-- Reindexing used to compare a single shift by `a + b` with successive shifts. -/
theorem addIndex (n a b : ℤ) : n + (a + b) = (n + b) + a := sorry

/-- The component comparing a shift by `a + b` with successive shifts by `a` and `b`. -/
def addApp (M : DifferentialGradedModule.{u, v} A) (a b : ℤ) :
    shift M (a + b) ≅ shift (shift M a) b where
  hom :=
    { hom := fun n ↦ ModuleCat.castLinearMap (congrArg M.X (addIndex n a b)) LinearMap.id
      comm_d := sorry
      comm_smul := sorry }
  inv :=
    { hom := fun n ↦ ModuleCat.castLinearMap (congrArg M.X (addIndex n a b).symm) LinearMap.id
      comm_d := sorry
      comm_smul := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward additive comparison is degreewise transport along `addIndex`. -/
@[simp] theorem addApp_hom_hom (M : DifferentialGradedModule.{u, v} A)
    (a b n : ℤ) :
    (addApp M a b).hom.hom n =
      ModuleCat.castLinearMap (congrArg M.X (addIndex n a b)) LinearMap.id := sorry

/-- The inverse additive comparison is degreewise transport along the reverse of `addIndex`. -/
@[simp] theorem addApp_inv_hom (M : DifferentialGradedModule.{u, v} A)
    (a b n : ℤ) :
    (addApp M a b).inv.hom n =
      ModuleCat.castLinearMap (congrArg M.X (addIndex n a b).symm) LinearMap.id := sorry

/-- The additive shift comparison is natural in the differential graded module. -/
def add (A : CochainDGAlgebra R) (a b : ℤ) :
    functor.{u, v} A (a + b) ≅ functor.{u, v} A a ⋙ functor.{u, v} A b :=
  NatIso.ofComponents (fun M ↦ addApp M a b) (fun _ ↦ sorry)

/-- Coherent core data for integer shifts of right differential graded modules. -/
def core (A : CochainDGAlgebra R) :
    ShiftMkCore (DifferentialGradedModule.{u, v} A) ℤ where
  F := functor.{u, v} A
  zero := zero A
  add := add A
  assoc_hom_app := sorry
  zero_add_hom_app := sorry
  add_zero_hom_app := sorry

/-- Right differential graded modules carry their canonical coherent integer shift. -/
@[implicit_reducible] instance hasShift (A : CochainDGAlgebra R) :
    HasShift (DifferentialGradedModule.{u, v} A) ℤ :=
  hasShiftMk (DifferentialGradedModule.{u, v} A) ℤ (core A)

/-- The abstract shift functor is the explicit differential graded module shift functor. -/
theorem shiftFunctor_eq (A : CochainDGAlgebra R) (k : ℤ) :
    CategoryTheory.shiftFunctor (DifferentialGradedModule.{u, v} A) k =
      functor.{u, v} A k := sorry

/-- Shifting a sum of right-DG-module morphisms is the sum of their shifts. -/
@[simp]
theorem shiftMap_add {M N : DifferentialGradedModule.{u, v} A}
    (f g : M ⟶ N) (k : ℤ) :
    shiftMap (f + g) k = shiftMap f k + shiftMap g k := sorry

/-- Shifting an `R`-multiple of a right-DG-module morphism preserves the scalar action. -/
@[simp]
theorem shiftMap_smul {M N : DifferentialGradedModule.{u, v} A}
    (r : R) (f : M ⟶ N) (k : ℤ) :
    shiftMap (r • f) k = r • shiftMap f k := sorry

/-- Every integer shift of differential graded modules is additive. -/
instance shiftFunctor_additive (A : CochainDGAlgebra R) (k : ℤ) :
    (CategoryTheory.shiftFunctor (DifferentialGradedModule.{u, v} A) k).Additive := sorry

/-- Every integer shift of differential graded modules is `R`-linear. -/
@[stacks 09JL "linearity of right-DG-module shifts"]
instance shiftFunctor_linear (A : CochainDGAlgebra R) (k : ℤ) :
    Functor.Linear R
      (CategoryTheory.shiftFunctor (DifferentialGradedModule.{u, v} A) k) := sorry

namespace Comp

/-- The explicit shift functor on the closed degree-zero category. -/
def functor (A : CochainDGAlgebra R) (k : ℤ) :
    DifferentialGradedCategory.Comp R (DifferentialGradedModule.{u, v} A) ⥤
      DifferentialGradedCategory.Comp R (DifferentialGradedModule.{u, v} A) where
  obj M := ⟨M.obj[k]⟩
  map f := homToCompHom (shiftMap (compHomToHom f) k)
  map_id := sorry
  map_comp := sorry

/-- The closed-category shift retains the explicitly shifted underlying module. -/
@[simp] theorem functor_obj (A : CochainDGAlgebra R)
    (M : DifferentialGradedCategory.Comp R (DifferentialGradedModule.{u, v} A)) (k : ℤ) :
    (functor.{u, v} A k).obj M = ⟨M.obj[k]⟩ := sorry

/-- The closed-category shift maps a representative through the module shift. -/
@[simp] theorem functor_map (A : CochainDGAlgebra R)
    {M N : DifferentialGradedCategory.Comp R (DifferentialGradedModule.{u, v} A)}
    (f : M ⟶ N) (k : ℤ) :
    (functor.{u, v} A k).map f = homToCompHom (shiftMap (compHomToHom f) k) := sorry

/-- The equivalence into closed degree-zero maps intertwines the explicit shifts. -/
def inducedIso (A : CochainDGAlgebra R) (k : ℤ) :
    toComp.{u, v} A ⋙ functor.{u, v} A k ≅
      Shift.functor.{u, v} A k ⋙ toComp.{u, v} A :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ sorry)

/-- The closed degree-zero category inherits its integer shift from ordinary module maps. -/
@[implicit_reducible] instance hasShift (A : CochainDGAlgebra R) :
    HasShift (DifferentialGradedCategory.Comp R (DifferentialGradedModule.{u, v} A)) ℤ :=
  HasShift.induced (toComp.{u, v} A) ℤ (functor.{u, v} A) (inducedIso.{u, v} A)

/-- The functor to closed degree-zero maps commutes with the induced integer shifts. -/
instance toCompCommShift (A : CochainDGAlgebra R) : (toComp.{u, v} A).CommShift ℤ :=
  Functor.CommShift.ofInduced
    (toComp.{u, v} A) ℤ (functor.{u, v} A) (inducedIso.{u, v} A)

/-- The abstract closed-category shift is the explicit closed shift functor. -/
theorem shiftFunctor_eq (A : CochainDGAlgebra R) (k : ℤ) :
    CategoryTheory.shiftFunctor
        (DifferentialGradedCategory.Comp R (DifferentialGradedModule.{u, v} A)) k =
      functor.{u, v} A k := sorry

/-- Every integer shift on the closed degree-zero category is additive. -/
instance shiftFunctor_additive (A : CochainDGAlgebra R) (k : ℤ) :
    (CategoryTheory.shiftFunctor
      (DifferentialGradedCategory.Comp R (DifferentialGradedModule.{u, v} A)) k).Additive := sorry

/-- Every integer shift on the closed degree-zero category is `R`-linear. -/
@[stacks 09JL "linearity of closed right-DG-module shifts"]
instance shiftFunctor_linear (A : CochainDGAlgebra R) (k : ℤ) :
    Functor.Linear R
      (CategoryTheory.shiftFunctor
        (DifferentialGradedCategory.Comp R (DifferentialGradedModule.{u, v} A)) k) := sorry

end Comp

namespace K

/-- Shifting a closed representative respects DG homotopy. -/
theorem map_sound {M N : DifferentialGradedModule.{u, v} A}
    {f g : CompHom M N} (k : ℤ) (h : Homotopic M N f g) :
    (homToCompHom (shiftMap (compHomToHom f) k)).toHomotopyClass =
      (homToCompHom (shiftMap (compHomToHom g) k)).toHomotopyClass := sorry

/-- Shift a morphism in the DG homotopy category by shifting a closed representative. -/
def map {M N : DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A)}
    (f : M ⟶ N) (k : ℤ) :
    (⟨M.obj[k]⟩ : DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A)) ⟶
      (⟨N.obj[k]⟩ : DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A)) :=
  Quotient.lift
    (fun g : CompHom M.obj N.obj ↦
      (homToCompHom (shiftMap (compHomToHom g) k)).toHomotopyClass)
    (fun _ _ h ↦ map_sound k h) f

/-- The explicit shift functor on the DG homotopy category. -/
def functor (A : CochainDGAlgebra R) (k : ℤ) :
    DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A) ⥤
      DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A) where
  obj M := ⟨M.obj[k]⟩
  map f := map f k
  map_id := sorry
  map_comp := sorry

/-- The homotopy-category shift retains the explicitly shifted underlying module. -/
@[simp] theorem functor_obj (A : CochainDGAlgebra R)
    (M : DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A)) (k : ℤ) :
    (functor.{u, v} A k).obj M = ⟨M.obj[k]⟩ := sorry

/-- The homotopy-category shift of a represented map is represented by the shifted map. -/
@[simp] theorem map_rep (A : CochainDGAlgebra R)
    {M N : DifferentialGradedModule.{u, v} A} (f : CompHom M N) (k : ℤ) :
    map f.toHomotopyClass k =
      (homToCompHom (shiftMap (compHomToHom f) k)).toHomotopyClass := sorry

/-- The quotient functor intertwines the explicit shifts. -/
def inducedIso (A : CochainDGAlgebra R) (k : ℤ) :
    (DifferentialGradedCategory.Comp.inKFunctor :
        DifferentialGradedCategory.Comp R (DifferentialGradedModule.{u, v} A) ⥤
          DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A)) ⋙
        functor.{u, v} A k ≅
      CategoryTheory.shiftFunctor
          (DifferentialGradedCategory.Comp R (DifferentialGradedModule.{u, v} A)) k ⋙
        (DifferentialGradedCategory.Comp.inKFunctor :
          DifferentialGradedCategory.Comp R (DifferentialGradedModule.{u, v} A) ⥤
            DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A)) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ sorry)

/-- The DG homotopy category inherits its integer shift from closed maps. -/
@[implicit_reducible] instance hasShift (A : CochainDGAlgebra R) :
    HasShift (DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A)) ℤ :=
  HasShift.induced
    (DifferentialGradedCategory.Comp.inKFunctor :
      DifferentialGradedCategory.Comp R (DifferentialGradedModule.{u, v} A) ⥤
        DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A))
    ℤ (functor.{u, v} A) (inducedIso.{u, v} A)

/-- The quotient functor to the DG homotopy category commutes with integer shifts. -/
instance inKFunctorCommShift (A : CochainDGAlgebra R) :
    (DifferentialGradedCategory.Comp.inKFunctor :
      DifferentialGradedCategory.Comp R (DifferentialGradedModule.{u, v} A) ⥤
        DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A)).CommShift ℤ :=
  Functor.CommShift.ofInduced
    (DifferentialGradedCategory.Comp.inKFunctor :
      DifferentialGradedCategory.Comp R (DifferentialGradedModule.{u, v} A) ⥤
        DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A))
    ℤ (functor.{u, v} A) (inducedIso.{u, v} A)

/-- The abstract homotopy-category shift is the explicit quotient shift functor. -/
theorem shiftFunctor_eq (A : CochainDGAlgebra R) (k : ℤ) :
    CategoryTheory.shiftFunctor
        (DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A)) k =
      functor.{u, v} A k := sorry

/-- Every integer shift on the DG homotopy category is additive. -/
instance shiftFunctor_additive (A : CochainDGAlgebra R) (k : ℤ) :
    (CategoryTheory.shiftFunctor
      (DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A)) k).Additive := sorry

/-- Every integer shift on the DG homotopy category is `R`-linear. -/
@[stacks 09JL "linearity of right-DG-module homotopy shifts"]
instance shiftFunctor_linear (A : CochainDGAlgebra R) (k : ℤ) :
    Functor.Linear R
      (CategoryTheory.shiftFunctor
        (DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A)) k) := sorry

end K

/-- The direct functor from differential graded modules to their DG homotopy category commutes
with the canonical integer shifts. -/
instance toKCommShift (A : CochainDGAlgebra R) : (toK.{u, v} A).CommShift ℤ :=
  Functor.CommShift.comp (toComp.{u, v} A)
    (DifferentialGradedCategory.Comp.inKFunctor :
      DifferentialGradedCategory.Comp R (DifferentialGradedModule.{u, v} A) ⥤
        DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A))

end DifferentialGradedModule.Shift
