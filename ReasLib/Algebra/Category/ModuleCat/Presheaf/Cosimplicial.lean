module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.BaseChange
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Modules over cosimplicial commutative algebras

This file defines modules over a cosimplicial commutative algebra, their canonical
base-change maps, and the full subcategory of cartesian modules.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

namespace CosimplicialAlgebra

variable {R : Type u} [CommRing R]

/-- The commutative-ring presheaf on `SimplexCategoryᵒᵖ` underlying a cosimplicial
commutative `R`-algebra. -/
abbrev commRingPresheaf (A : CosimplicialObject (CommAlgCat.{u} R)) :
    (SimplexCategoryᵒᵖ)ᵒᵖ ⥤ CommRingCat.{u} :=
  unopUnop SimplexCategory ⋙ A ⋙ forget₂ (CommAlgCat.{u} R) CommRingCat.{u}

/-- Modules over a cosimplicial commutative `R`-algebra, viewed as modules over its
double-opposite ring presheaf. -/
abbrev Module (A : CosimplicialObject (CommAlgCat.{u} R)) :=
  PresheafOfModules.{u} (ringPresheaf (commRingPresheaf A))

namespace Module

/-- Evaluation of a module over a cosimplicial algebra at a simplex. -/
abbrev eval {A : CosimplicialObject (CommAlgCat.{u} R)} (M : Module A)
    (n : SimplexCategory) :
    ModuleCat.{u} ((ringPresheaf (commRingPresheaf A)).obj (op (op n))) :=
  M.obj (op (op n))

/-- The scalar-extension comparison induced by a simplex morphism. -/
noncomputable def baseChangeMap {A : CosimplicialObject (CommAlgCat.{u} R)}
    (M : Module A) {n m : SimplexCategory} (f : n ⟶ m) :
    (PresheafOfModules.BaseChange.functor (commRingPresheaf A) f.op.op).obj M ⟶
      eval M m :=
  PresheafOfModules.BaseChange.map (commRingPresheaf A) M f.op.op

/-- A module over a cosimplicial algebra is cartesian when all of its canonical
scalar-extension comparisons are isomorphisms. -/
def IsCartesian {A : CosimplicialObject (CommAlgCat.{u} R)} (M : Module A) : Prop :=
  PresheafOfModules.BaseChange.compatible (commRingPresheaf A) M

/-- Cartesianness is the pointwise isomorphism condition for the named base-change maps. -/
theorem isCartesian_iff {A : CosimplicialObject (CommAlgCat.{u} R)} (M : Module A) :
    IsCartesian M ↔
      ∀ {n m : SimplexCategory} (f : n ⟶ m), IsIso (baseChangeMap M f) := sorry

end Module

/-- The category of cartesian modules over a cosimplicial commutative algebra. -/
abbrev CartesianModule (A : CosimplicialObject (CommAlgCat.{u} R)) :=
  ObjectProperty.FullSubcategory (fun M : Module A ↦ Module.IsCartesian M)

namespace CartesianModule

/-- The underlying module of a cartesian module satisfies the cartesian condition. -/
theorem isCartesian {A : CosimplicialObject (CommAlgCat.{u} R)}
    (M : CartesianModule A) : Module.IsCartesian M.obj :=
  M.property

/-- Every base-change comparison of a cartesian module is an isomorphism; the witness is the
cartesian property carried by the object. -/
instance baseChangeMap_isIso {A : CosimplicialObject (CommAlgCat.{u} R)}
    (M : CartesianModule A) {n m : SimplexCategory} (f : n ⟶ m) :
    IsIso (Module.baseChangeMap M.obj f) :=
  M.property f.op.op

/-- The canonical base-change isomorphism of a cartesian module. -/
noncomputable def baseChangeIso {A : CosimplicialObject (CommAlgCat.{u} R)}
    (M : CartesianModule A) {n m : SimplexCategory} (f : n ⟶ m) :
    (PresheafOfModules.BaseChange.functor (commRingPresheaf A) f.op.op).obj M.obj ≅
      Module.eval M.obj m :=
  asIso (Module.baseChangeMap M.obj f)

/-- The forward map of `baseChangeIso` is the canonical base-change comparison. -/
theorem baseChangeIso_hom {A : CosimplicialObject (CommAlgCat.{u} R)}
    (M : CartesianModule A) {n m : SimplexCategory} (f : n ⟶ m) :
    (baseChangeIso M f).hom = Module.baseChangeMap M.obj f := sorry

end CartesianModule

end CosimplicialAlgebra
