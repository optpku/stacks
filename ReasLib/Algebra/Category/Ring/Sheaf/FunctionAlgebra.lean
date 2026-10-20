module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Ring-valued functions on a sheaf

Natural functions from a sheaf of sets to a ring sheaf form a commutative ring under
pointwise operations. A specified constant chart identifies this ring with the product of
rings of sections, using the actual constant-sheaf adjunction in both directions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
universe u v w r

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The commutative ring of natural functions, as native flat sections over elements. -/
abbrev FunctionAlgebra (F : Sheaf J (Type w)) (O : Sheaf J CommRingCat.{r}) :=
  RingCat.sectionsSubring
    (CategoryOfElements.π F.obj ⋙ O.obj ⋙ forget₂ CommRingCat.{r} RingCat.{r})

namespace FunctionAlgebra

variable (F : Sheaf J (Type w)) (O : Sheaf J CommRingCat.{r})

instance : CommRing (FunctionAlgebra F O) :=
  @Subring.toCommRing (∀ j : F.obj.Elements, O.obj.obj j.1) inferInstance
    (RingCat.sectionsSubring
      (CategoryOfElements.π F.obj ⋙ O.obj ⋙ forget₂ CommRingCat.{r} RingCat.{r}))

/-- Evaluate a natural function at an actual section of the set-valued sheaf. -/
def eval (a : FunctionAlgebra F O) (U : Cᵒᵖ) (x : F.obj.obj U) : O.obj.obj U :=
  a.val (F.obj.elementsMk U x)

/-- Precomposition by a sheaf morphism acts contravariantly on natural functions. -/
def precomp {F' : Sheaf J (Type w)} (φ : F' ⟶ F) :
    FunctionAlgebra F O →+* FunctionAlgebra F' O where
  toFun a := ⟨fun j ↦ eval F O a j.1 (φ.hom.app j.1 j.2), by sorry⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' := sorry
  map_mul' := sorry

/-- Precomposition evaluates at the image of the input section. -/
@[simp]
theorem precomp_eval {F' : Sheaf J (Type w)} (φ : F' ⟶ F)
    (a : FunctionAlgebra F O) (U : Cᵒᵖ) (x : F'.obj.obj U) :
    eval F' O (precomp F O φ a) U x = eval F O a U (φ.hom.app U x) := rfl

/-- Precomposition by the identity leaves each natural function unchanged. -/
@[simp]
theorem precomp_id : precomp F O (𝟙 F) = RingHom.id _ := by sorry

/-- Precomposition reverses composition of sheaf morphisms. -/
theorem precomp_comp {F' F'' : Sheaf J (Type w)} (φ : F' ⟶ F) (ψ : F'' ⟶ F') :
    precomp F O (ψ ≫ φ) = (precomp F' O ψ).comp (precomp F O φ) := by sorry

/-- A specified sheaf isomorphism gives the actual two inverse precomposition maps. -/
def precompEquiv {F' : Sheaf J (Type w)} (e : F' ≅ F) :
    FunctionAlgebra F O ≃+* FunctionAlgebra F' O where
  toFun := precomp F O e.hom
  invFun := precomp F' O e.inv
  left_inv := sorry
  right_inv := sorry
  map_add' := (precomp F O e.hom).map_add
  map_mul' := (precomp F O e.hom).map_mul

section Coordinates

variable (F : Sheaf J (Type (max w r)))

/-- The underlying ring sheaf with its values explicitly lifted to the input universe. -/
def coefficients : Sheaf J (Type (max w r)) :=
  ⟨O.obj ⋙ forget CommRingCat.{r} ⋙ uliftFunctor.{w, r}, by sorry⟩

/-- Natural functions are exactly sheaf morphisms to the lifted underlying ring sheaf. -/
def homEquiv : FunctionAlgebra F O ≃ (F ⟶ coefficients.{u, v, w, r} O) where
  toFun a := ObjectProperty.homMk
    { app := fun U ↦ TypeCat.ofHom (fun x ↦ ULift.up (eval F O a U x))
      naturality := sorry }
  invFun φ := ⟨fun j ↦ (φ.hom.app j.1 j.2).down, by sorry⟩
  left_inv := sorry
  right_inv := sorry

variable [HasWeakSheafify J (Type (max w r))]

/-- A supplied constant chart gives product coordinates through the constant-sheaf adjunction. -/
def chartEquiv {E : Type (max w r)} (e : F ≅ (constantSheaf J (Type (max w r))).obj E)
    {T : C} (hT : IsTerminal T) : FunctionAlgebra F O ≃+* (E → O.obj.obj (op T)) where
  toFun a x :=
    (((constantSheafAdj J (Type (max w r)) hT).homEquiv E (coefficients O))
      (e.inv ≫ homEquiv (F := F) (O := O) a) x).down
  invFun f := (homEquiv (F := F) (O := O)).symm
    (e.hom ≫ ((constantSheafAdj J (Type (max w r)) hT).homEquiv E
      (coefficients O)).symm (TypeCat.ofHom (fun x ↦ ULift.up (f x))))
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry
  map_mul' := sorry

end Coordinates

end FunctionAlgebra
end CategoryTheory.Sheaf
