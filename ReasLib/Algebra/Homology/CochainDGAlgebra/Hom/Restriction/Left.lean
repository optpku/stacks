module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.FromModules
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Opposite
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction of Scalars for Left Differential Graded Modules

Restriction of scalars for left differential graded modules is obtained canonically by changing
handedness, restricting the resulting right module along the opposite DGA homomorphism, and
changing handedness back.  This avoids a second implementation of the action and its Koszul signs.

The file also names the derived category of left DG modules and the canonical functor into it.
-/

@[expose] public section

noncomputable section

universe u v w x y

open CategoryTheory

namespace CochainDGAlgebra.Hom

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R} {E : CochainDGAlgebra.{u, w} R}
  {F : CochainDGAlgebra.{u, x} R}

/-- Restriction of scalars of a left differential graded `E`-module along `φ : Hom A E`,
constructed through right modules over opposite DGAs. -/
def restrictLeftModule (φ : Hom A E) (M : LeftDifferentialGradedModule.{u, y} E) :
    LeftDifferentialGradedModule.{u, y} A :=
  LeftDifferentialGradedModule.unop (φ.opposite.restrictModule M.op)

/-- Left restriction of scalars preserves every underlying graded `R`-module. -/
@[simp]
theorem restrictLeftModule_X (φ : Hom A E)
    (M : LeftDifferentialGradedModule.{u, y} E) (n : ℤ) :
    (φ.restrictLeftModule M).X n = M.X n := sorry

/-- Left restriction of scalars preserves the differential in every degree. -/
@[simp]
theorem restrictLeftModule_d (φ : Hom A E)
    (M : LeftDifferentialGradedModule.{u, y} E) (n : ℤ) :
    (φ.restrictLeftModule M).d n = M.d n := sorry

/-- The restricted left action is obtained by applying `φ` to the algebra input. -/
@[simp]
theorem restrictLeftModule_smul (φ : Hom A E)
    (M : LeftDifferentialGradedModule.{u, y} E)
    (i p : ℤ) (a : A.X i) (x : M.X p) :
    (φ.restrictLeftModule M).smul i p a x = M.smul i p (φ i a) x := sorry

/-- Restriction of scalars on morphisms of left differential graded modules, obtained by
changing handedness on the original morphism before and after right restriction. -/
def restrictLeftHom (φ : Hom A E)
    {M N : LeftDifferentialGradedModule.{u, y} E} (f : M ⟶ N) :
    φ.restrictLeftModule M ⟶ φ.restrictLeftModule N :=
  LeftDifferentialGradedModule.Hom.unop
    (φ.opposite.restrictHom (LeftDifferentialGradedModule.Hom.op f))

/-- Restricting a left DG-module morphism preserves every degreewise linear map. -/
@[simp]
theorem restrictLeftHom_hom (φ : Hom A E)
    {M N : LeftDifferentialGradedModule.{u, y} E} (f : M ⟶ N) (n : ℤ) :
    (φ.restrictLeftHom f).hom n = f.hom n := sorry

/-- Restricting a left DG-module morphism preserves its values on homogeneous elements. -/
@[simp]
theorem restrictLeftHom_apply (φ : Hom A E)
    {M N : LeftDifferentialGradedModule.{u, y} E} (f : M ⟶ N)
    (n : ℤ) (x : M.X n) :
    (φ.restrictLeftHom f).hom n x = f.hom n x := sorry

/-- The ordinary restriction-of-scalars functor on left differential graded modules. -/
@[stacks 0GZ7 "restriction of scalars for left differential graded modules"]
def restrictLeftFunctor (φ : Hom A E) :
    LeftDifferentialGradedModule.{u, y} E ⥤
      LeftDifferentialGradedModule.{u, y} A :=
  LeftDifferentialGradedModule.opFunctor E ⋙
    φ.opposite.restrictFunctor ⋙ LeftDifferentialGradedModule.unopFunctor A

/-- The left restriction functor acts on objects by `restrictLeftModule`. -/
@[simp]
theorem restrictLeftFunctor_obj (φ : Hom A E)
    (M : LeftDifferentialGradedModule.{u, y} E) :
    φ.restrictLeftFunctor.obj M = φ.restrictLeftModule M := sorry

/-- The left restriction functor acts on morphisms by `restrictLeftHom`. -/
@[simp]
theorem restrictLeftFunctor_map (φ : Hom A E)
    {M N : LeftDifferentialGradedModule.{u, y} E} (f : M ⟶ N) :
    φ.restrictLeftFunctor.map f = φ.restrictLeftHom f := sorry

/-- The degreewise map of the left restriction functor is the original map. -/
@[simp]
theorem restrictLeftFunctor_map_hom (φ : Hom A E)
    {M N : LeftDifferentialGradedModule.{u, y} E} (f : M ⟶ N) (n : ℤ) :
    (φ.restrictLeftFunctor.map f).hom n = f.hom n := sorry

/-- The left restriction functor preserves values on homogeneous elements. -/
@[simp]
theorem restrictLeftFunctor_map_apply (φ : Hom A E)
    {M N : LeftDifferentialGradedModule.{u, y} E} (f : M ⟶ N)
    (n : ℤ) (x : M.X n) :
    (φ.restrictLeftFunctor.map f).hom n x = f.hom n x := sorry

/-- Restricting a left DG-module morphism preserves identity morphisms. -/
theorem restrictLeftHom_id (φ : Hom A E)
    (M : LeftDifferentialGradedModule.{u, y} E) :
    φ.restrictLeftHom (𝟙 M) = 𝟙 (φ.restrictLeftModule M) := sorry

/-- Restricting left DG-module morphisms preserves composition. -/
theorem restrictLeftHom_comp (φ : Hom A E)
    {L M N : LeftDifferentialGradedModule.{u, y} E}
    (f : L ⟶ M) (g : M ⟶ N) :
    φ.restrictLeftHom (f ≫ g) = φ.restrictLeftHom f ≫ φ.restrictLeftHom g := sorry

/-- Restricting along the identity DGA homomorphism leaves a left DG module unchanged. -/
theorem restrictLeftModule_id (A : CochainDGAlgebra.{u, v} R)
    (M : LeftDifferentialGradedModule.{u, y} A) :
    restrictLeftModule (Hom.id A) M = M := sorry

/-- Left restriction along a composite DGA homomorphism is iterated restriction of scalars. -/
theorem restrictLeftModule_comp (ψ : Hom E F) (φ : Hom A E)
    (M : LeftDifferentialGradedModule.{u, y} F) :
    (Hom.comp ψ φ).restrictLeftModule M =
      φ.restrictLeftModule (ψ.restrictLeftModule M) := sorry

/-- The left restriction functor along an identity DGA homomorphism is the identity functor. -/
theorem restrictLeftFunctor_id (A : CochainDGAlgebra.{u, v} R) :
    restrictLeftFunctor (Hom.id A) = 𝟭 (LeftDifferentialGradedModule.{u, y} A) := sorry

/-- Left restriction functors compose in the contravariant order of DGA homomorphisms. -/
theorem restrictLeftFunctor_comp (ψ : Hom E F) (φ : Hom A E) :
    (Hom.comp ψ φ).restrictLeftFunctor =
      ψ.restrictLeftFunctor ⋙ φ.restrictLeftFunctor := sorry

end CochainDGAlgebra.Hom

namespace LeftDifferentialGradedModule

variable {R : Type u} [CommRing R]

namespace Derived

/-- The derived category of left differential graded `A`-modules, modeled canonically as the
derived category of right differential graded `A.opposite`-modules. -/
abbrev Category (A : CochainDGAlgebra.{u, v} R) :=
  DifferentialGradedModule.Derived.Category.{u, y} A.opposite

end Derived

/-- The canonical functor from left differential graded modules to their derived category. -/
@[stacks 0GZ7 "canonical functor from left DG modules to their derived category"]
noncomputable def toDerived (A : CochainDGAlgebra.{u, v} R) :
    LeftDifferentialGradedModule.{u, y} A ⥤ Derived.Category A :=
  opFunctor A ⋙ DifferentialGradedModule.Derived.fromModules A.opposite

/-- A left DG module is represented in its derived category by its opposite right module. -/
@[simp]
theorem toDerived_obj (A : CochainDGAlgebra.{u, v} R)
    (M : LeftDifferentialGradedModule.{u, y} A) :
    (toDerived A).obj M =
      (DifferentialGradedModule.Derived.fromModules A.opposite).obj M.op := sorry

/-- The canonical left-module-to-derived functor maps a morphism through its opposite right
module morphism. -/
@[simp]
theorem toDerived_map (A : CochainDGAlgebra.{u, v} R)
    {M N : LeftDifferentialGradedModule.{u, y} A} (f : M ⟶ N) :
    (toDerived A).map f =
      (DifferentialGradedModule.Derived.fromModules A.opposite).map
        (LeftDifferentialGradedModule.Hom.op f) := sorry

end LeftDifferentialGradedModule
