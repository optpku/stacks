/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.CompositionHomotopy
public import ReasLib.Algebra.Homology.DifferentialGradedModule.DifferentialGraded

/-!
# Restriction of Scalars for Differential Graded Modules

This leaf packages restriction of scalars along a homomorphism of cochain
differential graded algebras.  It exposes the construction at the module,
ordinary-category, differential-graded-category, closed-category, and
homotopy-category levels. Derived restriction is owned by the separate `Restriction.Derived`
leaf, so this foundational construction does not depend on derived-functor machinery.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MorphismProperty
open DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

noncomputable section

universe u v w x y

namespace CochainDGAlgebra.Hom

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R} {E : CochainDGAlgebra.{u, w} R}
  {F : CochainDGAlgebra.{u, x} R}

/-- Restriction of scalars of a right differential graded `E`-module along `φ : Hom A E`. -/
@[stacks 09LD "restriction of scalars on differential graded modules"]
def restrictModule (φ : Hom A E) (M : DifferentialGradedModule.{u, y} E) :
    DifferentialGradedModule.{u, y} A where
  X := M.X
  d := M.d
  smul n m :=
    { toFun := fun x ↦
        { toFun := fun a ↦ M.smul n m x (φ m a)
          map_add' := sorry
          map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry }
  d_sq := M.d_sq
  smul_one := sorry
  smul_mul := sorry
  comm_d := sorry

/-- Restriction of scalars preserves every underlying graded `R`-module. -/
@[simp, stacks 09LD "restriction preserves underlying graded modules"]
theorem restrictModule_X (φ : Hom A E) (M : DifferentialGradedModule.{u, y} E) (n : ℤ) :
    (φ.restrictModule M).X n = M.X n := sorry

/-- Restriction of scalars preserves the differential in every degree. -/
@[simp, stacks 09LD "restriction preserves differentials"]
theorem restrictModule_d (φ : Hom A E) (M : DifferentialGradedModule.{u, y} E) (n : ℤ) :
    (φ.restrictModule M).d n = M.d n := sorry

/-- The restricted right action is obtained by applying `φ` to the algebra input. -/
@[simp, stacks 09LD "restricted module action formula"]
theorem restrictModule_smul (φ : Hom A E) (M : DifferentialGradedModule.{u, y} E)
    (n m : ℤ) (x : M.X n) (a : A.X m) :
    (φ.restrictModule M).smul n m x a = M.smul n m x (φ m a) := sorry

/-- Restriction of scalars on ordinary morphisms of differential graded modules. -/
@[stacks 09LD "restriction on differential graded module morphisms"]
def restrictHom (φ : Hom A E) {M N : DifferentialGradedModule.{u, y} E} (f : M ⟶ N) :
    φ.restrictModule M ⟶ φ.restrictModule N where
  hom := f.hom
  comm_d := f.comm_d
  comm_smul := sorry

/-- Restriction of a DG-module morphism preserves each degreewise linear map. -/
@[simp, stacks 09LD "restriction preserves morphism components"]
theorem restrictHom_hom (φ : Hom A E) {M N : DifferentialGradedModule.{u, y} E}
    (f : M ⟶ N) (n : ℤ) :
    (φ.restrictHom f).hom n = f.hom n := sorry

/-- Restriction of a DG-module morphism preserves its action on homogeneous elements. -/
@[simp, stacks 09LD "restriction preserves morphism evaluation"]
theorem restrictHom_apply (φ : Hom A E) {M N : DifferentialGradedModule.{u, y} E}
    (f : M ⟶ N)
    (n : ℤ) (x : M.X n) : (φ.restrictHom f).hom n x = f.hom n x := sorry

/-- Restriction of scalars on arbitrary homogeneous right-linear maps. -/
@[stacks 09LD "restriction on homogeneous module maps"]
def restrictGradedHom (φ : Hom A E) {M N : DifferentialGradedModule.{u, y} E} {k : ℤ}
    (f : DifferentialGradedModule.GradedHom E M N k) :
    DifferentialGradedModule.GradedHom A (φ.restrictModule M) (φ.restrictModule N) k :=
  ⟨f.1, sorry⟩

/-- Restriction of a homogeneous map preserves its degreewise values. -/
@[simp, stacks 09LD "restriction preserves homogeneous map evaluation"]
theorem restrictGradedHom_apply (φ : Hom A E)
    {M N : DifferentialGradedModule.{u, y} E} {k : ℤ}
    (f : DifferentialGradedModule.GradedHom E M N k) (n : ℤ) (x : M.X n) :
    φ.restrictGradedHom f n x = f n x := sorry

/-- The ordinary restriction-of-scalars functor on categories of differential graded modules. -/
@[stacks 09LD "ordinary restriction-of-scalars functor"]
def restrictFunctor (φ : Hom A E) :
    DifferentialGradedModule.{u, y} E ⥤ DifferentialGradedModule.{u, y} A where
  obj M := φ.restrictModule M
  map f := restrictHom φ f
  map_id := sorry
  map_comp := sorry

/-- The ordinary restriction functor acts on objects by `restrictModule`. -/
@[simp, stacks 09LD "ordinary restriction functor on objects"]
theorem restrictFunctor_obj (φ : Hom A E) (M : DifferentialGradedModule.{u, y} E) :
    (φ.restrictFunctor.obj M) = φ.restrictModule M := sorry

/-- The ordinary restriction functor acts on morphisms by `restrictHom`. -/
@[simp, stacks 09LD "ordinary restriction functor on morphisms"]
theorem restrictFunctor_map (φ : Hom A E) {M N : DifferentialGradedModule.{u, y} E}
    (f : M ⟶ N) :
    (φ.restrictFunctor.map f) = φ.restrictHom f := sorry

/-- The degreewise linear map of the ordinary restriction functor is the original map. -/
@[simp, stacks 09LD "ordinary restriction functor components"]
theorem restrictFunctor_map_hom (φ : Hom A E)
    {M N : DifferentialGradedModule.{u, y} E} (f : M ⟶ N)
    (n : ℤ) : ((φ.restrictFunctor.map f).hom n) = f.hom n := sorry

/-- Lemma 22.26.9 (restriction of scalars): a homomorphism `φ : Hom A E` induces a differential
graded functor from right differential graded `E`-modules to right differential graded
`A`-modules. -/
@[stacks 09LD "restriction differential graded functor"]
def restrictDgFunctor (φ : Hom A E) :
    DgFunctor R (DifferentialGradedModule.{u, y} E)
      (DifferentialGradedModule.{u, y} A) where
  obj M := φ.restrictModule M
  map f := restrictGradedHom φ f
  map_add := sorry
  map_smul := sorry
  map_d := sorry
  map_id := sorry
  map_comp := sorry

/-- The restriction DG functor acts on objects by the explicitly restricted module. -/
@[simp, stacks 09LD "restriction differential graded functor on objects"]
theorem restrictDgFunctor_obj (φ : Hom A E) (M : DifferentialGradedModule.{u, y} E) :
    (φ.restrictDgFunctor.obj M) = φ.restrictModule M := sorry

/-- The restriction DG functor acts on homogeneous maps by `restrictGradedHom`. -/
@[simp, stacks 09LD "restriction differential graded functor on homogeneous maps"]
theorem restrictDgFunctor_map (φ : Hom A E)
    {M N : DifferentialGradedModule.{u, y} E} {k : ℤ}
    (f : DifferentialGradedModule.GradedHom E M N k) :
    (φ.restrictDgFunctor.map f) = φ.restrictGradedHom f := sorry

/-- The restriction DG functor preserves every homogeneous map's degreewise values. -/
@[simp, stacks 09LD "restriction differential graded functor evaluation"]
theorem restrictDgFunctor_map_apply (φ : Hom A E)
    {M N : DifferentialGradedModule.{u, y} E} {k : ℤ}
    (f : DifferentialGradedModule.GradedHom E M N k) (n : ℤ) (x : M.X n) :
    φ.restrictDgFunctor.map f n x = f n x := sorry

/-- The restriction DG functor induces the expected object map on closed degree-zero morphisms. -/
@[simp, stacks 09LD "restriction on closed morphism objects"]
theorem restrictDgFunctor_mapComp_obj (φ : Hom A E)
    (M : Comp R (DifferentialGradedModule.{u, y} E)) :
    (φ.restrictDgFunctor.mapComp).obj M =
      (⟨φ.restrictModule M.obj⟩ : Comp R (DifferentialGradedModule.{u, y} A)) := sorry

/-- The closed morphism induced by restriction has the original degree-zero component. -/
@[simp, stacks 09LD "restriction on closed morphisms"]
theorem restrictDgFunctor_mapCompHom_val (φ : Hom A E)
    {M N : DifferentialGradedModule.{u, y} E}
    (f : CompHom M N) :
    (DgFunctor.mapCompHom φ.restrictDgFunctor f).val = φ.restrictGradedHom f.val := sorry

/-- The `Comp` functor induced by restriction maps a closed morphism through `mapCompHom`. -/
@[simp, stacks 09LD "restriction closed-category functor map"]
theorem restrictDgFunctor_mapComp_map (φ : Hom A E)
    {M N : DifferentialGradedModule.{u, y} E}
    (f : CompHom M N) :
    (φ.restrictDgFunctor.mapComp).map f = DgFunctor.mapCompHom φ.restrictDgFunctor f := sorry

/-- The restriction DG functor induces the expected object map on homotopy categories. -/
@[simp, stacks 09LD "restriction on homotopy-category objects"]
theorem restrictDgFunctor_mapK_obj (φ : Hom A E)
    (M : K R (DifferentialGradedModule.{u, y} E)) :
    ((φ.restrictDgFunctor).mapK.obj M).obj = φ.restrictModule M.obj := sorry

/-- Restriction sends a represented homotopy class to the class of the restricted morphism. -/
@[simp, stacks 09LD "restriction on represented homotopy classes"]
theorem restrictDgFunctor_mapK_map_toHomotopyClass (φ : Hom A E)
    {M N : DifferentialGradedModule.{u, y} E}
    (f : CompHom M N) :
    (φ.restrictDgFunctor.mapK).map f.toHomotopyClass =
      (DgFunctor.mapCompHom φ.restrictDgFunctor f).toHomotopyClass := sorry

/-- Restriction after the canonical passage from `Comp` to `K` is represented by the restricted
closed morphism. -/
@[simp, stacks 09LD "restriction on homotopy-category morphisms"]
theorem restrictDgFunctor_mapK_map_inK (φ : Hom A E)
    {M N : Comp R (DifferentialGradedModule.{u, y} E)}
    (f : M ⟶ N) :
    (φ.restrictDgFunctor.mapK).map f.inK =
      ((φ.restrictDgFunctor.mapComp).map f).inK := sorry

/-- Restricting along the identity homomorphism leaves a DG module unchanged. -/
@[stacks 09LD "restriction along identity"]
theorem restrictModule_id (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, y} A) :
    restrictModule (Hom.id A) M = M := sorry

/-- Restriction along a composite DGA homomorphism is iterated restriction of scalars. -/
@[stacks 09LD "restriction along a composite homomorphism"]
theorem restrictModule_comp (ψ : Hom E F) (φ : Hom A E)
    (M : DifferentialGradedModule.{u, y} F) :
    (Hom.comp ψ φ).restrictModule M = φ.restrictModule (ψ.restrictModule M) := sorry

/-- The ordinary restriction functor along an identity DGA homomorphism is the identity functor. -/
@[stacks 09LD "ordinary restriction identity law"]
theorem restrictFunctor_id (A : CochainDGAlgebra.{u, v} R) :
    restrictFunctor (Hom.id A) = 𝟭 (DifferentialGradedModule.{u, y} A) := sorry

/-- Restriction functors compose in the contravariant order of DGA homomorphisms. -/
@[stacks 09LD "ordinary restriction composition law"]
theorem restrictFunctor_comp (ψ : Hom E F) (φ : Hom A E) :
    (Hom.comp ψ φ).restrictFunctor = ψ.restrictFunctor ⋙ φ.restrictFunctor := sorry

/-- The DG restriction functor along an identity DGA homomorphism is the identity DG functor. -/
@[stacks 09LD "differential graded restriction identity law"]
theorem restrictDgFunctor_id (A : CochainDGAlgebra.{u, v} R) :
    restrictDgFunctor (Hom.id A) =
      DgFunctor.id R (DifferentialGradedModule.{u, y} A) := sorry

/-- DG restriction functors compose in the contravariant order of DGA homomorphisms. -/
@[stacks 09LD "differential graded restriction composition law"]
theorem restrictDgFunctor_comp (ψ : Hom E F) (φ : Hom A E) :
    (Hom.comp ψ φ).restrictDgFunctor =
      φ.restrictDgFunctor.comp ψ.restrictDgFunctor := sorry

/-- The functor on closed degree-zero morphisms induced by a composite restriction is the
composite of the two induced closed-category functors. -/
@[stacks 09LD "closed-category restriction composition law"]
theorem restrictDgFunctor_mapComp_comp (ψ : Hom E F) (φ : Hom A E) :
    (Hom.comp ψ φ).restrictDgFunctor.mapComp =
      ψ.restrictDgFunctor.mapComp ⋙ φ.restrictDgFunctor.mapComp := sorry

/-- The functor on homotopy categories induced by a composite restriction is the composite of
the two induced homotopy-category functors. -/
@[stacks 09LD "homotopy-category restriction composition law"]
theorem restrictDgFunctor_mapK_comp (ψ : Hom E F) (φ : Hom A E) :
    (Hom.comp ψ φ).restrictDgFunctor.mapK =
      ψ.restrictDgFunctor.mapK ⋙ φ.restrictDgFunctor.mapK := sorry

end CochainDGAlgebra.Hom
