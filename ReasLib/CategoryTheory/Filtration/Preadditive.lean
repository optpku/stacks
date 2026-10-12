/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.ZeroMorphisms
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Preadditive Structure on Filtered Objects

When `C` is preadditive, the category `FilteredObject C` inherits a preadditive structure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace FilteredObject

variable {X Y : FilteredObject C}

theorem add_preserves (f g : X ⟶ Y) (i : ℤ) :
    (Y.filtration.stage i).Factors ((X.filtration.stage i).arrow ≫ (f.hom + g.hom)) := by
  simpa [Hom.stageMap, Category.assoc, Preadditive.add_comp, Preadditive.comp_add] using
    Subobject.factors_comp_arrow
      (f.stageMap i + g.stageMap i : (X.filtration.stage i : C) ⟶ Y.filtration.stage i)

theorem neg_preserves (f : X ⟶ Y) (i : ℤ) :
    (Y.filtration.stage i).Factors ((X.filtration.stage i).arrow ≫ (-f.hom)) := by
  simpa [Hom.stageMap, Category.assoc, Preadditive.neg_comp, Preadditive.comp_neg] using
    Subobject.factors_comp_arrow
      (-f.stageMap i : (X.filtration.stage i : C) ⟶ Y.filtration.stage i)

theorem sub_preserves (f g : X ⟶ Y) (i : ℤ) :
    (Y.filtration.stage i).Factors ((X.filtration.stage i).arrow ≫ (f.hom - g.hom)) := by
  simpa [Hom.stageMap, Category.assoc, Preadditive.sub_comp, Preadditive.comp_sub] using
    Subobject.factors_comp_arrow
      (f.stageMap i - g.stageMap i : (X.filtration.stage i : C) ⟶ Y.filtration.stage i)

theorem nsmul_preserves (n : ℕ) (f : X ⟶ Y) (i : ℤ) :
    (Y.filtration.stage i).Factors ((X.filtration.stage i).arrow ≫ (n • f.hom)) := by
  simpa [Hom.stageMap, Category.assoc, Preadditive.nsmul_comp, Preadditive.comp_nsmul] using
    Subobject.factors_comp_arrow
      (n • f.stageMap i : (X.filtration.stage i : C) ⟶ Y.filtration.stage i)

theorem zsmul_preserves (n : ℤ) (f : X ⟶ Y) (i : ℤ) :
    (Y.filtration.stage i).Factors ((X.filtration.stage i).arrow ≫ (n • f.hom)) := by
  simpa [Hom.stageMap, Category.assoc, Preadditive.zsmul_comp, Preadditive.comp_zsmul] using
    Subobject.factors_comp_arrow
      (n • f.stageMap i : (X.filtration.stage i : C) ⟶ Y.filtration.stage i)

instance : Add (X ⟶ Y) where
  add f g := { hom := f.hom + g.hom, preserves := add_preserves f g }

instance : Neg (X ⟶ Y) where
  neg f := { hom := -f.hom, preserves := neg_preserves f }

instance : Sub (X ⟶ Y) where
  sub f g := { hom := f.hom - g.hom, preserves := sub_preserves f g }

instance : SMul ℕ (X ⟶ Y) where
  smul n f := { hom := n • f.hom, preserves := nsmul_preserves n f }

instance : SMul ℤ (X ⟶ Y) where
  smul n f := { hom := n • f.hom, preserves := zsmul_preserves n f }

@[simp] theorem add_hom (f g : X ⟶ Y) : (f + g).hom = f.hom + g.hom := rfl
@[simp] theorem neg_hom (f : X ⟶ Y) : (-f).hom = -f.hom := rfl
@[simp] theorem sub_hom (f g : X ⟶ Y) : (f - g).hom = f.hom - g.hom := rfl
@[simp] theorem nsmul_hom (n : ℕ) (f : X ⟶ Y) : (n • f).hom = n • f.hom := rfl
@[simp] theorem zsmul_hom (n : ℤ) (f : X ⟶ Y) : (n • f).hom = n • f.hom := rfl

omit [Preadditive C] in
theorem hom_injective : Function.Injective (Hom.hom : (X ⟶ Y) → (X.obj ⟶ Y.obj)) :=
  fun _ _ h => (forget : FilteredObject C ⥤ C).map_injective h

instance : AddCommGroup (X ⟶ Y) :=
  Function.Injective.addCommGroup Hom.hom hom_injective
    zero_hom (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[stacks 0122]
instance : Preadditive (FilteredObject C) where
  add_comp _ _ _ f f' g := by
    apply hom_injective
    change (f + f').hom ≫ g.hom = (f ≫ g + f' ≫ g).hom
    simp only [add_hom, comp_hom]
    exact Preadditive.add_comp _ _ _ f.hom f'.hom g.hom
  comp_add _ _ _ f g g' := by
    apply hom_injective
    change f.hom ≫ (g + g').hom = (f ≫ g + f ≫ g').hom
    simp only [add_hom, comp_hom]
    exact Preadditive.comp_add _ _ _ f.hom g.hom g'.hom

@[stacks 0122 "filtered-object forgetful functor is additive"]
instance : (FilteredObject.forget : FilteredObject C ⥤ C).Additive where
  map_add {_ _} _ _ := rfl

end FilteredObject

#synth Preadditive (FilteredObject C)
#synth (FilteredObject.forget : FilteredObject C ⥤ C).Additive

end CategoryTheory
