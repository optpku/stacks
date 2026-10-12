/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.DegreeZero

/-!
# Closed Degree-Zero Morphisms in a Differential Graded Category

This leaf constructs the category `Comp` of objects of a differential graded
category and its closed degree-zero morphisms.  The homotopy quotient belongs
to `DifferentialGraded/Homotopy`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace DifferentialGradedCategory

variable {R : Type u} [CommRing R]
variable {C : Type v}

open scoped DifferentialGradedCategory

/-- Definition 22.26.3 (Tag `09L7`): the object type of the category of closed degree-zero
morphisms. -/
@[stacks 09L7]
structure Comp (R : Type u) [CommRing R] (C : Type v) where
  /-- The underlying object of the differential graded category. -/
  obj : C

namespace Comp

/-- A `Comp` object can be used as its underlying object of the differential graded category. -/
instance : CoeTC (Comp R C) C where
  coe X := X.obj

/-- Constructing a `Comp` object and coercing it back recovers the original object. -/
@[stacks 09L7 "closed-category object coercion", simp]
theorem coe_mk (X : C) : ((⟨X⟩ : Comp R C) : C) = X := rfl

end Comp

variable [D : DifferentialGradedCategory R C]

/-- Closedness of the zero degree-zero morphism. -/
@[stacks 09L7 "zero closed degree-zero morphism"]
theorem compHomSubmodule_zero_mem (X Y : C) : D.d 0 (0 : X ⟶[0] Y) = 0 := sorry

/-- Closed degree-zero morphisms are closed under addition. -/
@[stacks 09L7 "addition of closed degree-zero morphisms"]
theorem compHomSubmodule_add_mem {X Y : C} {f g : X ⟶[0] Y}
    (hf : D.d 0 f = 0) (hg : D.d 0 g = 0) : D.d 0 (f + g) = 0 := sorry

/-- Closed degree-zero morphisms are closed under scalar multiplication. -/
@[stacks 09L7 "scalar multiplication of closed degree-zero morphisms"]
theorem compHomSubmodule_smul_mem {X Y : C} (r : R) {f : X ⟶[0] Y}
    (hf : D.d 0 f = 0) : D.d 0 (r • f) = 0 := sorry

/-- The closed degree-zero morphisms form a submodule of the degree-zero hom-space. -/
@[stacks 09L7 "closed degree-zero hom submodule"]
def compHomSubmodule (X Y : C) : Submodule R (X ⟶[0] Y) where
  carrier := { f | D.d 0 f = 0 }
  zero_mem' := compHomSubmodule_zero_mem X Y
  add_mem' := fun hf hg ↦ compHomSubmodule_add_mem hf hg
  smul_mem' := fun r _ hf ↦ compHomSubmodule_smul_mem r hf

/-- Closed degree-zero morphisms in a differential graded category. -/
@[stacks 09L7 "closed degree-zero hom type"]
abbrev CompHom (X Y : C) : Type w :=
  compHomSubmodule X Y

namespace CompHom

/-- A `CompHom` is closed by definition. -/
@[stacks 09L7 "closedness of a closed degree-zero hom", simp]
theorem closed {X Y : C} (f : CompHom X Y) : D.d 0 (f : X ⟶[0] Y) = 0 := sorry

end CompHom

/-- The underlying morphism of a closed degree-zero morphism constructed from explicit data. -/
@[stacks 09L7 "underlying morphism of a closed hom constructor", simp]
theorem CompHom.coe_mk {X Y : C} (f : X ⟶[0] Y) (hf) :
    ((⟨f, hf⟩ : CompHom X Y) : X ⟶[0] Y) = f := sorry

/-- Closed degree-zero morphisms are determined by their underlying homogeneous morphisms. -/
@[stacks 09L7 "extensionality of closed degree-zero homs", ext]
theorem CompHom.ext {X Y : C} {f g : CompHom X Y} (h : f.val = g.val) : f = g := sorry

/-- The underlying morphism of the zero closed degree-zero morphism. -/
@[stacks 09L7 "underlying zero closed hom", simp]
theorem CompHom.zero_val {X Y : C} :
    ((0 : CompHom X Y) : X ⟶[0] Y) = 0 := sorry

/-- The underlying morphism of a sum of closed degree-zero morphisms. -/
@[stacks 09L7 "underlying sum of closed homs", simp]
theorem CompHom.add_val {X Y : C} (f g : CompHom X Y) :
    ((f + g : CompHom X Y) : X ⟶[0] Y) = (f : X ⟶[0] Y) + (g : X ⟶[0] Y) := sorry

/-- The underlying morphism of the negative of a closed degree-zero morphism. -/
@[stacks 09L7 "underlying negation of a closed hom", simp]
theorem CompHom.neg_val {X Y : C} (f : CompHom X Y) :
    ((-f : CompHom X Y) : X ⟶[0] Y) = -(f : X ⟶[0] Y) := sorry

/-- The underlying morphism of a difference of closed degree-zero morphisms. -/
@[stacks 09L7 "underlying difference of closed homs", simp]
theorem CompHom.sub_val {X Y : C} (f g : CompHom X Y) :
    ((f - g : CompHom X Y) : X ⟶[0] Y) = (f : X ⟶[0] Y) - (g : X ⟶[0] Y) := sorry

/-- The underlying morphism of a scalar multiple of a closed degree-zero morphism. -/
@[stacks 09L7 "underlying scalar multiple of a closed hom", simp]
theorem CompHom.smul_val {X Y : C} (r : R) (f : CompHom X Y) :
    ((r • f : CompHom X Y) : X ⟶[0] Y) = r • (f : X ⟶[0] Y) := sorry

/-- The identity degree-zero morphism is closed. -/
@[stacks 09L7 "closedness of the degree-zero identity"]
theorem compHom_id_closed (X : C) : D.d 0 (D.id X) = 0 := sorry

/-- The composite of closed degree-zero morphisms is closed. -/
@[stacks 09L7 "closedness under composition"]
theorem compHom_comp_closed {X Y Z : C} (f : CompHom X Y) (g : CompHom Y Z) :
    D.d 0 (D.comp g.val f.val) = 0 := sorry

/-- The identity closed degree-zero morphism. -/
@[stacks 09L7 "identity closed degree-zero morphism"]
def CompHom.id (X : C) : CompHom X X :=
  ⟨D.id X, compHom_id_closed X⟩

/-- The underlying degree-zero morphism of `CompHom.id`. -/
@[stacks 09L7 "underlying identity closed hom", simp]
theorem CompHom.id_val (X : C) : (CompHom.id X).val = D.id X := sorry

/-- The composite of two closed degree-zero morphisms. -/
@[stacks 09L7 "composition of closed degree-zero morphisms"]
def CompHom.comp {X Y Z : C} (f : CompHom X Y) (g : CompHom Y Z) : CompHom X Z :=
  ⟨D.comp g.val f.val, compHom_comp_closed f g⟩

/-- The underlying degree-zero morphism of `CompHom.comp`. -/
@[stacks 09L7 "underlying composition of closed homs", simp]
theorem CompHom.comp_val {X Y Z : C} (f : CompHom X Y) (g : CompHom Y Z) :
    (CompHom.comp f g).val = D.comp g.val f.val := sorry

/-- Left identity in the category of closed degree-zero morphisms. -/
@[stacks 09L7 "left identity for closed hom composition"]
theorem compCategory_id_comp {X Y : Comp R C} (f : CompHom X.obj Y.obj) :
    CompHom.comp (CompHom.id X.obj) f = f := sorry

/-- Right identity in the category of closed degree-zero morphisms. -/
@[stacks 09L7 "right identity for closed hom composition"]
theorem compCategory_comp_id {X Y : Comp R C} (f : CompHom X.obj Y.obj) :
    CompHom.comp f (CompHom.id Y.obj) = f := sorry

/-- Associativity in the category of closed degree-zero morphisms. -/
@[stacks 09L7 "associativity of closed hom composition"]
theorem compCategory_assoc {W X Y Z : Comp R C} (f : CompHom W.obj X.obj)
    (g : CompHom X.obj Y.obj) (h : CompHom Y.obj Z.obj) :
    CompHom.comp (CompHom.comp f g) h = CompHom.comp f (CompHom.comp g h) := sorry

/-- The category of objects of a differential graded category and closed degree-zero morphisms. -/
@[stacks 09L7 "category of closed degree-zero morphisms"]
instance compCategory : Category (Comp R C) where
  Hom X Y := CompHom X.obj Y.obj
  id X := CompHom.id X.obj
  comp f g := CompHom.comp f g
  id_comp := compCategory_id_comp
  comp_id := compCategory_comp_id
  assoc := compCategory_assoc

namespace Comp

/-- The forgetful functor from closed degree-zero morphisms to all degree-zero morphisms. -/
@[stacks 09L7 "forgetful functor from closed to degree-zero morphisms"]
def forgetToDegreeZero : Comp R C ⥤ DegreeZero R C where
  obj X := ⟨X.obj⟩
  map f := f.val
  map_id X := CompHom.id_val X.obj
  map_comp f g := CompHom.comp_val f g

/-- `forgetToDegreeZero` preserves the underlying object. -/
@[stacks 09L7 "forgetful functor object computation", simp]
theorem forgetToDegreeZero_obj (X : Comp R C) :
    forgetToDegreeZero.obj X = ⟨X.obj⟩ := sorry

/-- `forgetToDegreeZero` sends a closed morphism to its underlying degree-zero morphism. -/
@[stacks 09L7 "forgetful functor morphism computation", simp]
theorem forgetToDegreeZero_map {X Y : Comp R C} (f : X ⟶ Y) :
    forgetToDegreeZero.map f = f.val := sorry

end Comp

/-- The additive commutative group on each hom-space of `Comp`. -/
@[stacks 09L7 "additive hom groups of the closed category"]
abbrev compHomAddCommGroup (X Y : Comp R C) : AddCommGroup (CompHom X.obj Y.obj) :=
  inferInstance

/-- Addition is compatible with right composition of closed degree-zero morphisms. -/
@[stacks 09L7 "right distributivity in the closed category"]
theorem compPreadditive_add_comp (X Y Z : Comp R C) (f f' : CompHom X.obj Y.obj)
    (g : CompHom Y.obj Z.obj) :
    CompHom.comp (f + f') g = CompHom.comp f g + CompHom.comp f' g := sorry

/-- Addition is compatible with left composition of closed degree-zero morphisms. -/
@[stacks 09L7 "left distributivity in the closed category"]
theorem compPreadditive_comp_add (X Y Z : Comp R C) (f : CompHom X.obj Y.obj)
    (g g' : CompHom Y.obj Z.obj) :
    CompHom.comp f (g + g') = CompHom.comp f g + CompHom.comp f g' := sorry

/-- The category of closed degree-zero morphisms is preadditive. -/
@[stacks 09L7 "preadditive structure on the closed category"]
instance compPreadditive : Preadditive (Comp R C) where
  homGroup X Y := compHomAddCommGroup X Y
  add_comp X Y Z f f' g := compPreadditive_add_comp X Y Z f f' g
  comp_add X Y Z f g g' := compPreadditive_comp_add X Y Z f g g'

/-- The canonical `R`-module structure on a hom-space of `Comp`. -/
@[stacks 09L7 "module structure on closed hom spaces"]
instance compHomModule (X Y : Comp R C) : Module R (X ⟶ Y) :=
  inferInstanceAs <| Module R (CompHom X.obj Y.obj)

/-- Scalar multiplication is compatible with postcomposition in `Comp`. -/
@[stacks 09L7 "postcomposition and scalar multiplication in the closed category"]
theorem compLinear_smul_comp (X Y Z : Comp R C) (r : R)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (r • f) ≫ g = r • (f ≫ g) := sorry

/-- Scalar multiplication is compatible with precomposition in `Comp`. -/
@[stacks 09L7 "precomposition and scalar multiplication in the closed category"]
theorem compLinear_comp_smul (X Y Z : Comp R C)
    (f : X ⟶ Y) (r : R) (g : Y ⟶ Z) :
    f ≫ (r • g) = r • (f ≫ g) := sorry

/-- The category of closed degree-zero morphisms is canonically `R`-linear. -/
@[stacks 09L7 "linear structure on the closed category"]
instance compLinear : Linear R (Comp R C) where
  homModule X Y := compHomModule X Y
  smul_comp := compLinear_smul_comp
  comp_smul := compLinear_comp_smul

namespace Comp

/-- The forgetful functor to all degree-zero morphisms preserves addition. -/
@[stacks 09L7 "forgetful functor preserves addition", simp]
theorem forgetToDegreeZero_map_add {X Y : Comp R C} (f g : X ⟶ Y) :
    forgetToDegreeZero.map (f + g) = forgetToDegreeZero.map f + forgetToDegreeZero.map g := sorry

/-- The forgetful functor to all degree-zero morphisms preserves scalar multiplication. -/
@[stacks 09L7 "forgetful functor preserves scalar multiplication", simp]
theorem forgetToDegreeZero_map_smul (r : R) {X Y : Comp R C} (f : X ⟶ Y) :
    forgetToDegreeZero.map (r • f) = r • forgetToDegreeZero.map f := sorry

/-- Forgetting closedness gives an additive functor on degree-zero categories. -/
@[stacks 09L7 "additivity of the closed-to-degree-zero forgetful functor"]
instance forgetToDegreeZero_additive : (forgetToDegreeZero : Comp R C ⥤ DegreeZero R C).Additive where
  map_add := fun {X Y} f g ↦ forgetToDegreeZero_map_add (X := X) (Y := Y) f g

/-- Forgetting closedness gives an `R`-linear functor on degree-zero categories. -/
@[stacks 09L7 "linearity of the closed-to-degree-zero forgetful functor"]
instance forgetToDegreeZero_linear :
    Functor.Linear R (forgetToDegreeZero : Comp R C ⥤ DegreeZero R C) where
  map_smul := fun {X Y} f r ↦ forgetToDegreeZero_map_smul r (X := X) (Y := Y) f

end Comp

end DifferentialGradedCategory
