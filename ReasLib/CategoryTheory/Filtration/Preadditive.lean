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

/-- The sum of two filtration-preserving morphisms preserves every filtration stage. -/
theorem add_preserves (f g : X ⟶ Y) (i : ℤ) :
    (Y.filtration.stage i).Factors ((X.filtration.stage i).arrow ≫ (f.hom + g.hom)) := by
  simpa [Hom.stageMap, Category.assoc, Preadditive.add_comp, Preadditive.comp_add] using
    Subobject.factors_comp_arrow
      (f.stageMap i + g.stageMap i : (X.filtration.stage i : C) ⟶ Y.filtration.stage i)

/-- The negative of a filtration-preserving morphism preserves every filtration stage. -/
theorem neg_preserves (f : X ⟶ Y) (i : ℤ) :
    (Y.filtration.stage i).Factors ((X.filtration.stage i).arrow ≫ (-f.hom)) := by
  simpa [Hom.stageMap, Category.assoc, Preadditive.neg_comp, Preadditive.comp_neg] using
    Subobject.factors_comp_arrow
      (-f.stageMap i : (X.filtration.stage i : C) ⟶ Y.filtration.stage i)

/-- The difference of two filtration-preserving morphisms preserves every filtration stage. -/
theorem sub_preserves (f g : X ⟶ Y) (i : ℤ) :
    (Y.filtration.stage i).Factors ((X.filtration.stage i).arrow ≫ (f.hom - g.hom)) := by
  simpa [Hom.stageMap, Category.assoc, Preadditive.sub_comp, Preadditive.comp_sub] using
    Subobject.factors_comp_arrow
      (f.stageMap i - g.stageMap i : (X.filtration.stage i : C) ⟶ Y.filtration.stage i)

/-- A natural multiple of a filtration-preserving morphism preserves every filtration stage. -/
theorem nsmul_preserves (n : ℕ) (f : X ⟶ Y) (i : ℤ) :
    (Y.filtration.stage i).Factors ((X.filtration.stage i).arrow ≫ (n • f.hom)) := by
  simpa [Hom.stageMap, Category.assoc, Preadditive.nsmul_comp, Preadditive.comp_nsmul] using
    Subobject.factors_comp_arrow
      (n • f.stageMap i : (X.filtration.stage i : C) ⟶ Y.filtration.stage i)

/-- An integer multiple of a filtration-preserving morphism preserves every filtration stage. -/
theorem zsmul_preserves (n : ℤ) (f : X ⟶ Y) (i : ℤ) :
    (Y.filtration.stage i).Factors ((X.filtration.stage i).arrow ≫ (n • f.hom)) := by
  simpa [Hom.stageMap, Category.assoc, Preadditive.zsmul_comp, Preadditive.comp_zsmul] using
    Subobject.factors_comp_arrow
      (n • f.stageMap i : (X.filtration.stage i : C) ⟶ Y.filtration.stage i)

/-- Addition of filtered morphisms is induced by addition of their underlying morphisms. -/
@[reducible] def add : Add (X ⟶ Y) where
  add f g := { hom := f.hom + g.hom, preserves := add_preserves f g }

/-- Negation of a filtered morphism is induced by negation of its underlying morphism. -/
@[reducible] def neg : Neg (X ⟶ Y) where
  neg f := { hom := -f.hom, preserves := neg_preserves f }

/-- Subtraction of filtered morphisms is induced by subtraction of their underlying morphisms. -/
@[reducible] def sub : Sub (X ⟶ Y) where
  sub f g := { hom := f.hom - g.hom, preserves := sub_preserves f g }

/-- Natural scalar multiplication of filtered morphisms is induced stagewise. -/
@[reducible] def nsmul : SMul ℕ (X ⟶ Y) where
  smul n f := { hom := n • f.hom, preserves := nsmul_preserves n f }

/-- Integer scalar multiplication of filtered morphisms is induced stagewise. -/
@[reducible] def zsmul : SMul ℤ (X ⟶ Y) where
  smul n f := { hom := n • f.hom, preserves := zsmul_preserves n f }

/-- The additive operation on filtered morphisms is canonical. -/
instance instAdd : Add (X ⟶ Y) := add
/-- Negation on filtered morphisms is canonical. -/
instance instNeg : Neg (X ⟶ Y) := neg
/-- Subtraction on filtered morphisms is canonical. -/
instance instSub : Sub (X ⟶ Y) := sub
/-- Natural scalar multiplication on filtered morphisms is canonical. -/
instance instNSMul : SMul ℕ (X ⟶ Y) := nsmul
/-- Integer scalar multiplication on filtered morphisms is canonical. -/
instance instZSMul : SMul ℤ (X ⟶ Y) := zsmul

/-- The underlying morphism of a sum is the sum of the underlying morphisms. -/
@[simp] theorem add_hom (f g : X ⟶ Y) : (f + g).hom = f.hom + g.hom := rfl
/-- The underlying morphism of a negative is the negative of the underlying morphism. -/
@[simp] theorem neg_hom (f : X ⟶ Y) : (-f).hom = -f.hom := rfl
/-- The underlying morphism of a difference is the difference of the underlying morphisms. -/
@[simp] theorem sub_hom (f g : X ⟶ Y) : (f - g).hom = f.hom - g.hom := rfl
/-- The underlying morphism of a natural multiple is the same multiple of the underlying map. -/
@[simp] theorem nsmul_hom (n : ℕ) (f : X ⟶ Y) : (n • f).hom = n • f.hom := rfl
/-- The underlying morphism of an integer multiple is the same multiple of the underlying map. -/
@[simp] theorem zsmul_hom (n : ℤ) (f : X ⟶ Y) : (n • f).hom = n • f.hom := rfl

omit [Preadditive C] in
/-- A filtered morphism is uniquely determined by its underlying morphism. -/
theorem hom_injective : Function.Injective (Hom.hom : (X ⟶ Y) → (X.obj ⟶ Y.obj)) :=
  fun _ _ h => (forget : FilteredObject C ⥤ C).map_injective h

/-- The filtered morphisms form an additive commutative group under the induced operations. -/
@[reducible] def addCommGroup : AddCommGroup (X ⟶ Y) :=
  Function.Injective.addCommGroup Hom.hom hom_injective
    zero_hom (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- The group instance supplies the canonical additive laws for filtered morphisms. -/
instance instAddCommGroup : AddCommGroup (X ⟶ Y) := addCommGroup

/-- The category of filtered objects over a preadditive category is preadditive. -/
@[reducible] def preadditive : Preadditive (FilteredObject C) where
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

/-- The canonical preadditive instance on filtered objects. -/
@[stacks 0122]
instance instPreadditive : Preadditive (FilteredObject C) := preadditive

/-- The forgetful functor from filtered objects preserves addition of morphisms. -/
@[stacks 0122 "filtered-object forgetful functor is additive"]
instance : (FilteredObject.forget : FilteredObject C ⥤ C).Additive where
  map_add {_ _} _ _ := rfl

end FilteredObject

end CategoryTheory
