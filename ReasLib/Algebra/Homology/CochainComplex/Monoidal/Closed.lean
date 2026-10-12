/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import ReasLib.CategoryTheory.GradedObject.Monoidal.Closed
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed structure on integer cochain complexes

@stack 0FRS

The internal Hom complex from `X` to `Y` has degree-`n` object
`∏ i, (X.X i ⟶[C] Y.X (i + n))`. Its differential is the graded commutator of
postcomposition by `Y.d` and precomposition by `X.d`. This file constructs the object and the
tensor/internal-Hom adjunction independently of rings, modules, sheaves, and bimodules.
-/

@[expose] public section

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace CategoryTheory.CochainComplex.InternalHom

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
variable [HasZeroObject C] [HasProductsOfShape ℤ C]
variable [∀ X Y : GradedObject ℤ C, GradedObject.HasTensor X Y]
variable [∀ X Y Z : GradedObject ℤ C, GradedObject.HasGoodTensor₁₂Tensor X Y Z]
variable [∀ X Y Z : GradedObject ℤ C, GradedObject.HasGoodTensorTensor₂₃ X Y Z]
variable [∀ X Y Z W : GradedObject ℤ C, GradedObject.HasTensor₄ObjExt X Y Z W]
variable [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X)]
variable [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X)]

/-- Reassociate the target differential degree in the internal Hom complex. -/
theorem postDegree (i n : ℤ) : i + n + 1 = i + (n + 1) := sorry

/-- Reassociate the source differential degree in the internal Hom complex. -/
theorem preDegree (i n : ℤ) : (i + 1) + n = i + (n + 1) := sorry

/-- The family whose product is degree `n` of the internal Hom complex. -/
noncomputable abbrev family (X Y : CochainComplex C ℤ) (n : ℤ) : ℤ → C :=
  GradedObject.InternalHom.family X.X Y.X n

/-- The underlying graded object of the internal Hom complex. -/
@[stacks 0FRS "underlying graded object of a cochain internal Hom"]
noncomputable abbrev gradedObj (X Y : CochainComplex C ℤ) : GradedObject ℤ C :=
  GradedObject.InternalHom.obj X.X Y.X

/-- Postcomposition by the target differential in one source degree. -/
noncomputable def postDifferential (X Y : CochainComplex C ℤ) (n i : ℤ) :
    gradedObj X Y n ⟶ (ihom (X.X i)).obj (Y.X (i + (n + 1))) :=
  Pi.π (family X Y n) i ≫
    (ihom (X.X i)).map (Y.d (i + n) (i + n + 1)) ≫
      eqToHom
        (congrArg (fun j ↦ (ihom (X.X i)).obj (Y.X j)) (postDegree i n))

/-- Precomposition by the source differential in one source degree. -/
noncomputable def preDifferential (X Y : CochainComplex C ℤ) (n i : ℤ) :
    gradedObj X Y n ⟶ (ihom (X.X i)).obj (Y.X (i + (n + 1))) :=
  CategoryTheory.MonoidalClosed.curry
    ((X.d i (i + 1) ▷ gradedObj X Y n) ≫
      (X.X (i + 1) ◁ Pi.π (family X Y n) (i + 1)) ≫
        (ihom.ev (X.X (i + 1))).app (Y.X ((i + 1) + n)) ≫
          eqToHom (congrArg Y.X (preDegree i n)))

/-- The graded-commutator differential on the internal Hom complex. -/
noncomputable def differential (X Y : CochainComplex C ℤ) (n : ℤ) :
    gradedObj X Y n ⟶ gradedObj X Y (n + 1) :=
  Pi.lift fun i ↦
    postDifferential X Y n i + (n + 1).negOnePow • preDifferential X Y n i

/-- Consecutive internal-Hom differentials compose to zero. -/
theorem differential_sq (X Y : CochainComplex C ℤ) (n : ℤ) :
    differential X Y n ≫ differential X Y (n + 1) = 0 := sorry

/-- The internal Hom complex with its explicit graded-commutator differential. -/
@[stacks 0FRS "cochain internal Hom object"]
noncomputable def obj (X Y : CochainComplex C ℤ) : CochainComplex C ℤ :=
  CochainComplex.of (gradedObj X Y) (differential X Y) (differential_sq X Y)

/-- Postcomposition by a cochain map on internal Hom complexes. -/
noncomputable def map (X : CochainComplex C ℤ) {Y Y' : CochainComplex C ℤ} (f : Y ⟶ Y') :
    obj X Y ⟶ obj X Y' where
  f n := GradedObject.InternalHom.map X.X f.f n
  comm' := sorry

/-- Internal Hom from a fixed cochain complex, functorial in the target complex. -/
@[stacks 0FRS "cochain internal Hom functor"]
noncomputable def functor (X : CochainComplex C ℤ) :
    CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj := obj X
  map := map X
  map_id := sorry
  map_comp := sorry

/-- Curry a cochain map into the explicit internal Hom complex. -/
noncomputable def curry {X Y Z : CochainComplex C ℤ} (f : X ⊗ Z ⟶ Y) :
    Z ⟶ obj X Y where
  f := GradedObject.InternalHom.curry f.f
  comm' := sorry

/-- Uncurry a cochain map out of the explicit internal Hom complex. -/
noncomputable def uncurry {X Y Z : CochainComplex C ℤ} (f : Z ⟶ obj X Y) :
    X ⊗ Z ⟶ Y where
  f := GradedObject.InternalHom.uncurry f.f
  comm' := sorry

/-- Tensor/internal-Hom currying for integer cochain complexes. -/
@[stacks 0FRS "cochain tensor-Hom equivalence"]
noncomputable def homEquiv (X Z Y : CochainComplex C ℤ) :
    (X ⊗ Z ⟶ Y) ≃ (Z ⟶ obj X Y) where
  toFun := curry
  invFun := uncurry
  left_inv := sorry
  right_inv := sorry

/-- Naturality data for the cochain tensor/internal-Hom equivalence. -/
noncomputable def coreHomEquiv (X : CochainComplex C ℤ) :
    Adjunction.CoreHomEquiv (tensorLeft X) (functor X) where
  homEquiv Z Y := homEquiv X Z Y
  homEquiv_naturality_left_symm := sorry
  homEquiv_naturality_right := sorry

/-- Tensoring by a cochain complex is left adjoint to its internal Hom functor. -/
@[stacks 0FRS "cochain tensor-Hom adjunction"]
noncomputable def adjunction (X : CochainComplex C ℤ) : tensorLeft X ⊣ functor X :=
  Adjunction.mkOfHomEquiv (coreHomEquiv X)

/-- The closed structure represented by the explicit cochain internal Hom. -/
@[implicit_reducible]
noncomputable def closed (X : CochainComplex C ℤ) : Closed X where
  rightAdj := functor X
  adj := adjunction X

/-- The canonical monoidal closed structure on integer cochain complexes. -/
@[stacks 0FRS "closed category of integer cochain complexes", instance_reducible]
noncomputable def monoidalClosed : MonoidalClosed (CochainComplex C ℤ) where
  closed := closed



end CategoryTheory.CochainComplex.InternalHom

end
