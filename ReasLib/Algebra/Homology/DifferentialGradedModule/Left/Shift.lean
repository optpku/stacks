module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Opposite
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Shift.Category
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Shifts of Left Differential Graded Modules

The shift of a left DG module is transported through the equivalence with right modules over the
opposite DGA.  This makes the Koszul sign in the shifted left action canonical rather than a
second ad hoc action.  The explicit shift is promoted to a coherent categorical shift and to an
autoequivalence for every integer.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open scoped DifferentialGradedModule

namespace LeftDifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra R}

/-- Definition 22.11.3 (0FQ1): the shift of a left DG module, transported from the canonical
shift of right modules over `A.opposite`. -/
@[stacks 0FQ1 "shift of a left differential graded module"]
def shift (M : LeftDifferentialGradedModule.{u, v} A) (k : ℤ) :
    LeftDifferentialGradedModule A :=
  unop (A := A) (DifferentialGradedModule.shift M.op k)

/-- Shift a morphism of left DG modules degreewise. -/
def shiftMap {M N : LeftDifferentialGradedModule.{u, v} A} (f : M ⟶ N) (k : ℤ) :
    shift M k ⟶ shift N k :=
  Hom.unop (A := A) (DifferentialGradedModule.shiftMap (Hom.op f) k)

/-- Reassociation from the target of the original left action to the corresponding component of
the shifted module. -/
theorem shiftSmulIndex (i p k : ℤ) : i + (p + k) = (i + p) + k := sorry

/-- The degree-`n` component of a shifted left DG module is `M.X (n + k)`. -/
@[simp]
theorem shift_X (M : LeftDifferentialGradedModule.{u, v} A) (k n : ℤ) :
    (shift M k).X n = M.X (n + k) := sorry

/-- The shifted differential is `(-1)^k d_M` after reindexing. -/
@[simp]
theorem shift_d (M : LeftDifferentialGradedModule.{u, v} A) (k n : ℤ) :
    (shift M k).d n =
      ModuleCat.castLinearMap (congrArg M.X (DifferentialGradedModule.shift_d_index n k))
        ((k.negOnePow : R) • M.d (n + k)) := sorry

/-- The action of a degree-`i` element on `M[k]` is twisted by the canonical Koszul sign
`(-1)^(i * k)`. -/
@[simp]
theorem shift_smul_apply (M : LeftDifferentialGradedModule.{u, v} A)
    (k i p : ℤ) (a : A.X i) (x : (shift M k).X p) :
    (shift M k).smul i p a x =
      cast (congrArg (fun n : ℤ ↦ (M.X n : Type v)) (shiftSmulIndex i p k))
        (((i * k).negOnePow : R) • M.smul i (p + k) a x) := sorry

/-- A shifted left-DG-module morphism is the original map in the reindexed degree. -/
@[simp]
theorem shiftMap_hom {M N : LeftDifferentialGradedModule.{u, v} A}
    (f : M ⟶ N) (k n : ℤ) :
    (shiftMap f k).hom n = f.hom (n + k) := sorry

/-- Shifting a left-DG-module morphism preserves identity morphisms. -/
@[simp]
theorem shiftMap_id (M : LeftDifferentialGradedModule.{u, v} A) (k : ℤ) :
    shiftMap (𝟙 M) k = 𝟙 (shift M k) := sorry

/-- Shifting a left-DG-module morphism preserves composition. -/
@[simp]
theorem shiftMap_comp {L M N : LeftDifferentialGradedModule.{u, v} A}
    (f : L ⟶ M) (g : M ⟶ N) (k : ℤ) :
    shiftMap (f ≫ g) k = shiftMap f k ≫ shiftMap g k := sorry

namespace Shift

/-- Shifting by a fixed integer is an endofunctor on left differential graded modules. -/
def functor (A : CochainDGAlgebra R) (k : ℤ) :
    LeftDifferentialGradedModule.{u, v} A ⥤ LeftDifferentialGradedModule.{u, v} A where
  obj M := shift M k
  map f := shiftMap f k
  map_id := sorry
  map_comp := sorry

/-- The left-DG-module shift functor uses the explicit shifted module on objects. -/
@[simp]
theorem functor_obj (A : CochainDGAlgebra R)
    (M : LeftDifferentialGradedModule.{u, v} A) (k : ℤ) :
    (functor.{u, v} A k).obj M = shift M k := sorry

/-- The left-DG-module shift functor uses the degreewise shifted map on morphisms. -/
@[simp]
theorem functor_map (A : CochainDGAlgebra R)
    {M N : LeftDifferentialGradedModule.{u, v} A} (f : M ⟶ N) (k : ℤ) :
    (functor.{u, v} A k).map f = shiftMap f k := sorry

/-- Recovering the left action intertwines a right-module shift with the explicit signed left
shift. -/
def unopIso (M : DifferentialGradedModule.{u, v} A.opposite) (k : ℤ) :
    shift (unop M) k ≅ unop (DifferentialGradedModule.shift M k) where
  hom := Hom.unop (DifferentialGradedModule.shiftMap (counitIso M).hom k)
  inv := Hom.unop (DifferentialGradedModule.shiftMap (counitIso M).inv k)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward handedness comparison for a shifted right module is the shifted counit in every
degree. -/
@[simp]
theorem unopIso_hom_hom (M : DifferentialGradedModule.{u, v} A.opposite)
    (k n : ℤ) :
    (unopIso M k).hom.hom n = (counitIso M).hom.hom (n + k) := sorry

/-- The inverse handedness comparison for a shifted right module is the shifted inverse counit in
every degree. -/
@[simp]
theorem unopIso_inv_hom (M : DifferentialGradedModule.{u, v} A.opposite)
    (k n : ℤ) :
    (unopIso M k).inv.hom n = (counitIso M).inv.hom (n + k) := sorry

/-- Recovering left actions intertwines the right-DG-module shift functor with the explicit
signed left-DG-module shift functor. -/
def unopFunctorIso (A : CochainDGAlgebra R) (k : ℤ) :
    unopFunctor A ⋙ functor.{u, v} A k ≅
      DifferentialGradedModule.Shift.functor A.opposite k ⋙ unopFunctor A :=
  NatIso.ofComponents (fun M ↦ unopIso M k) (fun _ ↦ sorry)

/-- Left differential graded modules carry the coherent integer shift induced through the
handedness equivalence from right modules over the opposite DGA. -/
@[implicit_reducible]
instance hasShift (A : CochainDGAlgebra R) :
    HasShift (LeftDifferentialGradedModule.{u, v} A) ℤ :=
  HasShift.induced (unopFunctor.{u, v} A) ℤ (functor.{u, v} A)
    (unopFunctorIso.{u, v} A)

/-- Recovering left actions commutes coherently with all integer shifts. -/
instance unopFunctorCommShift (A : CochainDGAlgebra R) :
    (unopFunctor.{u, v} A).CommShift ℤ :=
  Functor.CommShift.ofInduced (unopFunctor.{u, v} A) ℤ (functor.{u, v} A)
    (unopFunctorIso.{u, v} A)

/-- The shift comparison inferred for `unopFunctor` is the inverse of the comparison used to
induce the left-module shift. -/
@[simp]
theorem unopFunctor_commShiftIso (A : CochainDGAlgebra R) (k : ℤ) :
    (unopFunctor.{u, v} A).commShiftIso k = (unopFunctorIso.{u, v} A k).symm := sorry

/-- The abstract shift functor is the explicit left-DG-module shift functor. -/
theorem shiftFunctor_eq (A : CochainDGAlgebra R) (k : ℤ) :
    CategoryTheory.shiftFunctor (LeftDifferentialGradedModule.{u, v} A) k =
      functor.{u, v} A k := sorry

/-- Changing handedness identifies the shifted left module with the shift of the corresponding
right module over the opposite DGA. -/
def opIso (M : LeftDifferentialGradedModule.{u, v} A) (k : ℤ) :
    (shift M k).op ≅ DifferentialGradedModule.shift M.op k :=
  LeftDifferentialGradedModule.counitIso (DifferentialGradedModule.shift M.op k)

/-- The change-of-handedness functor intertwines the explicit left and right shift functors. -/
def opFunctorIso (A : CochainDGAlgebra R) (k : ℤ) :
    functor.{u, v} A k ⋙ opFunctor A ≅
      opFunctor A ⋙ DifferentialGradedModule.Shift.functor A.opposite k :=
  NatIso.ofComponents (fun M ↦ opIso M k) (fun _ ↦ sorry)

/-- Taking opposite actions commutes coherently with all integer shifts. -/
instance opFunctorCommShift (A : CochainDGAlgebra R) :
    (opFunctor.{u, v} A).CommShift ℤ where
  commShiftIso := opFunctorIso.{u, v} A
  commShiftIso_zero := sorry
  commShiftIso_add := sorry

/-- The automatically inferred shift comparison for `opFunctor` agrees with the explicit
handedness comparison. -/
@[simp]
theorem opFunctor_commShiftIso (A : CochainDGAlgebra R) (k : ℤ) :
    (opFunctor.{u, v} A).commShiftIso k = opFunctorIso.{u, v} A k := sorry

end Shift

end LeftDifferentialGradedModule
