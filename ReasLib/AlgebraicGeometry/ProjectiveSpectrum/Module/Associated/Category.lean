/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Graded.Finite.Abelian
public import ReasLib.Algebra.Group.Action.NatInt
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.Exact
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Tactic.CrossRefAttribute

/-!
# The associated-sheaf functor for finite graded modules

This file packages the existing associated module sheaf construction as functors on graded-module
categories and on coherent sheaves.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Proj.Associated

variable {A : Type u} [CommRing A]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]

/-- The associated module sheaf of a bundled integer-graded left module. -/
@[stacks 0BXF "associated module sheaf of a graded module"]
noncomputable def obj (M : GradedModule.Left 𝒜 ℤ) : (Proj 𝒜).Modules :=
  @Proj.AssociatedModule.sheaf ℤ A M _ _ _ _ M.moduleBase M.moduleAlgebra
    _ _ _ 𝒜 M.grading _ _

/-- The associated-sheaf morphism induced by a bundled graded-module morphism. -/
@[stacks 0BXF "associated module sheaf map"]
noncomputable def map {M N : GradedModule.Left 𝒜 ℤ} (f : M ⟶ N) :
    obj 𝒜 M ⟶ obj 𝒜 N :=
  @Proj.AssociatedModule.map ℤ A M N _ _ _ _ M.moduleBase M.moduleAlgebra
    _ N.moduleBase N.moduleAlgebra _ _ _ 𝒜 _ M.grading N.grading M.decomposition N.decomposition
    M.gradedSMul N.gradedSMul f.toLinearMap (fun _ _ hx ↦ f.map_mem hx)

/-- The associated-sheaf map induced by the identity module morphism is the identity. -/
@[stacks 0BXF "associated module sheaf map preserves identities"]
theorem map_id (M : GradedModule.Left 𝒜 ℤ) :
    map 𝒜 (𝟙 M) = 𝟙 (obj 𝒜 M) := sorry

/-- The associated-sheaf map induced by a composite is the composite of the associated maps. -/
@[stacks 0BXF "associated module sheaf map preserves composition"]
theorem map_comp {M N P : GradedModule.Left 𝒜 ℤ} (f : M ⟶ N) (g : N ⟶ P) :
    map 𝒜 (f ≫ g) = map 𝒜 f ≫ map 𝒜 g := sorry

/-- 0BXF: The associated module sheaf construction as a functor from integer-graded left
modules to modules on `Proj 𝒜`. -/
@[stacks 0BXF]
noncomputable def functor : GradedModule.Left 𝒜 ℤ ⥤ (Proj 𝒜).Modules where
  obj := obj 𝒜
  map := map 𝒜
  map_id := map_id 𝒜
  map_comp := map_comp 𝒜

/-- The associated-sheaf functor evaluates through the bundled-object constructor. -/
@[simp, stacks 0BXF "associated module sheaf functor on objects"]
theorem functor_obj (M : GradedModule.Left 𝒜 ℤ) :
    (functor 𝒜).obj M = obj 𝒜 M := sorry

/-- The associated-sheaf functor maps through the bundled-morphism constructor. -/
@[simp, stacks 0BXF "associated module sheaf functor on morphisms"]
theorem functor_map {M N : GradedModule.Left 𝒜 ℤ} (f : M ⟶ N) :
    (functor 𝒜).map f = map 𝒜 f := sorry

/-- The associated module sheaf functor restricted to finitely generated graded modules. -/
@[stacks 0BXF]
noncomputable def fgFunctor : GradedModule.Left.FG 𝒜 ℤ ⥤ (Proj 𝒜).Modules :=
  (GradedModule.Left.isFG 𝒜 ℤ).ι ⋙ functor 𝒜

/-- The finite associated-sheaf functor forgets finite generation before applying `obj`. -/
@[simp]
theorem fgFunctor_obj (M : GradedModule.Left.FG 𝒜 ℤ) :
    (fgFunctor 𝒜).obj M = obj 𝒜 M.obj := sorry

/-- The finite associated-sheaf functor forgets finite generation before applying `map`. -/
@[simp]
theorem fgFunctor_map {M N : GradedModule.Left.FG 𝒜 ℤ} (f : M ⟶ N) :
    (fgFunctor 𝒜).map f = map 𝒜 (M := M.obj) (N := N.obj) f.hom := sorry

/-- A finitely generated graded module has a coherent associated module sheaf over a Noetherian
graded ring. -/
theorem isCoherent [IsNoetherianRing A] (M : GradedModule.Left.FG 𝒜 ℤ) :
    SheafOfModules.IsCoherent ((fgFunctor 𝒜).obj M) := sorry

/-- 0BXF: The associated module sheaf construction lifted canonically to coherent sheaves. -/
@[stacks 0BXF]
noncomputable def coherentFunctor [IsNoetherianRing A] :
    GradedModule.Left.FG 𝒜 ℤ ⥤ RingedSpace.Coh (Proj 𝒜).toRingedSpace :=
  (SheafOfModules.isCoherent _).lift (fgFunctor 𝒜) (isCoherent 𝒜)

/-- The coherent associated-sheaf functor is exact. -/
@[stacks 0BXF]
theorem exact [IsNoetherianRing A] :
    exactFunctor (GradedModule.Left.FG 𝒜 ℤ)
      (RingedSpace.Coh (Proj 𝒜).toRingedSpace) (coherentFunctor 𝒜) := sorry

/-- 0BXF: The coherent associated-sheaf functor, bundled with its exactness. -/
@[stacks 0BXF]
noncomputable def exactFunctor [IsNoetherianRing A] :
    GradedModule.Left.FG 𝒜 ℤ ⥤ₑ RingedSpace.Coh (Proj 𝒜).toRingedSpace :=
  ⟨coherentFunctor 𝒜, exact 𝒜⟩

namespace FiniteType

/-- The coherent associated-sheaf exact functor when the graded ring is finite type over its
Noetherian degree-zero part. -/
@[stacks 0BXD]
noncomputable def exactFunctor [Algebra.FiniteType (𝒜 0) A]
    [IsNoetherianRing (𝒜 0)] :
    GradedModule.Left.FG 𝒜 ℤ ⥤ₑ RingedSpace.Coh (Proj 𝒜).toRingedSpace :=
  @AlgebraicGeometry.Proj.Associated.exactFunctor A _ 𝒜 _
    (Algebra.FiniteType.isNoetherianRing (𝒜 0) A)

/-- The finite-type exact functor has the canonical associated sheaf as its underlying object. -/
@[simp]
theorem exactFunctor_obj [Algebra.FiniteType (𝒜 0) A] [IsNoetherianRing (𝒜 0)]
    (M : GradedModule.Left.FG 𝒜 ℤ) :
    ((exactFunctor 𝒜).obj.obj M).obj = obj 𝒜 M.obj := sorry

/-- The finite-type exact functor has the canonical associated map as its underlying morphism. -/
@[simp]
theorem exactFunctor_map [Algebra.FiniteType (𝒜 0) A] [IsNoetherianRing (𝒜 0)]
    {M N : GradedModule.Left.FG 𝒜 ℤ} (f : M ⟶ N) :
    ((exactFunctor 𝒜).obj.map f).hom = map 𝒜 (M := M.obj) (N := N.obj) f.hom := sorry

end FiniteType

end AlgebraicGeometry.Proj.Associated
