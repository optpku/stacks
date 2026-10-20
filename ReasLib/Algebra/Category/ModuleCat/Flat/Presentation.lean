/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# The canonical finite-free presentation of a module

The diagram consists of all maps from the standard finite-free modules into the specified
module. Its colimit descent evaluates the rank-one representative of each element. Flatness
is needed only to make this concrete presentation filtered.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace ModuleCat.FlatPresentation

section Ring

variable (R : Type u) [Ring R]

/-- The standard finite-free modules in a chosen universe, with every linear map as a morphism. -/
abbrev StandardFree :=
  InducedCategory (ModuleCat.{max u v} R)
    (fun n : ℕ ↦ ModuleCat.of R (ULift.{v} (Fin n →₀ R)))

/-- The inclusion of the standard finite-free modules into all modules. -/
abbrev free : StandardFree.{u, v} R ⥤ ModuleCat.{max u v} R :=
  inducedFunctor (fun n : ℕ ↦ ModuleCat.of R (ULift.{v} (Fin n →₀ R)))

variable {R} (M : ModuleCat.{max u v} R)

/-- The index category of finite-free modules equipped with a map to `M`. -/
abbrev Index := CostructuredArrow (free.{u, v} R) M

/-- The presentation diagram forgets the structure map into `M`. -/
def diagram : Index M ⥤ ModuleCat.{max u v} R :=
  CostructuredArrow.proj (free.{u, v} R) M ⋙ free.{u, v} R

/-- Every object in the presentation is free. -/
instance diagram_obj_free (F : Index M) : Module.Free R ((diagram M).obj F) :=
  inferInstanceAs (Module.Free R (ULift.{v} (Fin F.left →₀ R)))

/-- Every object in the presentation is finite. -/
instance diagram_obj_finite (F : Index M) : Module.Finite R ((diagram M).obj F) :=
  inferInstanceAs (Module.Finite R (ULift.{v} (Fin F.left →₀ R)))

/-- The canonical cocone consists of the original maps into `M`. -/
def cocone : Cocone (diagram M) where
  pt := M
  ι :=
    { app := fun F ↦ F.hom
      naturality := fun _ _ f ↦ CostructuredArrow.w f }

/-- The rank-one presentation object whose basis element maps to `x`. -/
def element (x : M) : Index M :=
  CostructuredArrow.mk (C := StandardFree.{u, v} R) (S := free.{u, v} R) (T := M)
    (Y := (1 : ℕ))
    (ModuleCat.ofHom (X := (free.{u, v} R).obj (1 : ℕ)) (Y := M)
      ((Finsupp.linearCombination R (fun _ : Fin 1 ↦ x)).comp
        ULift.moduleEquiv.toLinearMap))

/-- The structure map of a rank-one representative sends its basis vector to the element. -/
@[simp]
theorem element_hom_single (x : M) :
    (element M x).hom (ULift.up (Finsupp.single (0 : Fin 1) 1)) = x := sorry

/-- Evaluate an arbitrary cocone at the rank-one representative of an element of `M`. -/
def descFun (c : Cocone (diagram M)) (x : M) : c.pt :=
  c.ι.app (element M x) (ULift.up (Finsupp.single (0 : Fin 1) 1))

/-- The universal descent is the linear map obtained by evaluating rank-one representatives. -/
def desc (c : Cocone (diagram M)) : M ⟶ c.pt :=
  ModuleCat.ofHom
    { toFun := descFun M c
      map_add' := sorry
      map_smul' := sorry }

/-- The universal map has the specified rank-one evaluation as its actual value. -/
@[simp]
theorem desc_apply (c : Cocone (diagram M)) (x : M) :
    desc M c x = c.ι.app (element M x) (ULift.up (Finsupp.single (0 : Fin 1) 1)) := rfl

/-- The universal descent agrees with each map of the supplied cocone. -/
@[reassoc]
theorem cocone_ι_desc (c : Cocone (diagram M)) (F : Index M) :
    (cocone M).ι.app F ≫ desc M c = c.ι.app F := sorry

/-- A map out of `M` is determined by its composites with all finite-free structure maps. -/
theorem desc_unique (c : Cocone (diagram M)) (f : M ⟶ c.pt)
    (hf : ∀ F : Index M, (cocone M).ι.app F ≫ f = c.ι.app F) :
    f = desc M c := sorry

/-- Every module is the colimit of its canonical finite-free presentation. -/
def isColimit : IsColimit (cocone M) where
  desc := desc M
  fac := cocone_ι_desc M
  uniq := desc_unique M

/-- The chosen colimit map is exactly the rank-one evaluation descent. -/
@[simp]
theorem isColimit_desc (c : Cocone (diagram M)) :
    (isColimit M).desc c = desc M c := rfl

end Ring

section CommRing

variable {R : Type u} [CommRing R] (M : ModuleCat.{max u v} R)

/-- Flatness makes the actual finite-free presentation category filtered. -/
instance index_isFiltered [Module.Flat R M] : IsFiltered (Index M) := sorry

end CommRing

end ModuleCat.FlatPresentation
