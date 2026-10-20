module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-!
# Explicit inverses of sectionwise bijective module-sheaf maps

The reverse section function searches the actual fiber of the specified map.
It selects a member only when that fiber is inhabited, and otherwise returns
the source module's zero. Bijectivity is used for the linearity and inverse
laws; it supplies no new section data to this function.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w r

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{r}} {M N : SheafOfModules.{w} R} (φ : M ⟶ N)

/-- Take a preimage from the actual section fiber, with zero outside the image. -/
def sectionPreimage (U : Cᵒᵖ) (y : N.val.obj U) : M.val.obj U := by
  classical
  exact if h : ∃ x : M.val.obj U, (φ.val.app U).hom x = y then h.choose else 0

/-- Outside the actual section image, the total preimage function returns zero. -/
theorem sectionPreimage_of_not_mem (U : Cᵒᵖ) (y : N.val.obj U)
    (hy : ¬ ∃ x : M.val.obj U, (φ.val.app U).hom x = y) :
    sectionPreimage φ U y = 0 := by
  classical
  simp only [sectionPreimage, dif_neg hy]

/-- On an inhabited fiber, the specified preimage function recovers its image. -/
theorem app_sectionPreimage (U : Cᵒᵖ) (y : N.val.obj U)
    (hy : ∃ x : M.val.obj U, (φ.val.app U).hom x = y) :
    (φ.val.app U).hom (sectionPreimage φ U y) = y := by
  classical
  dsimp [sectionPreimage]
  rw [dif_pos hy]
  exact hy.choose_spec

/-- Injectivity makes the selected preimage of an actual image the original section. -/
theorem sectionPreimage_app (U : Cᵒᵖ)
    (hφ : Function.Injective (φ.val.app U).hom) (x : M.val.obj U) :
    sectionPreimage φ U ((φ.val.app U).hom x) = x := by
  apply hφ
  exact app_sectionPreimage φ U _ ⟨x, rfl⟩

/-- The preimage function of a sectionwise bijective linear map preserves addition. -/
theorem sectionPreimage_add
    (U : Cᵒᵖ) (hφ : Function.Bijective (φ.val.app U).hom) (x y : N.val.obj U) :
    sectionPreimage φ U (x + y) = sectionPreimage φ U x + sectionPreimage φ U y := sorry

/-- The preimage function of a sectionwise bijective linear map preserves scalars. -/
theorem sectionPreimage_smul
    (U : Cᵒᵖ) (hφ : Function.Bijective (φ.val.app U).hom) (a : R.obj.obj U) (x : N.val.obj U) :
    sectionPreimage φ U (a • x) = a • sectionPreimage φ U x := sorry

/-- The linear reverse on sections has the specified actual fiber function. -/
def sectionInverse
    (U : Cᵒᵖ) (hφ : Function.Bijective (φ.val.app U).hom) :
    N.val.obj U ⟶ M.val.obj U :=
  ModuleCat.ofHom
    { toFun := sectionPreimage φ U
      map_add' := sectionPreimage_add φ U hφ
      map_smul' := fun a x ↦ sectionPreimage_smul φ U hφ a x }

/-- The specified section inverses commute with the existing restriction maps. -/
theorem sectionInverse_naturality
    (hφ : ∀ U : Cᵒᵖ, Function.Bijective (φ.val.app U).hom)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    N.val.map f ≫ (ModuleCat.restrictScalars (R.obj.map f).hom).map (sectionInverse φ V (hφ V)) =
      sectionInverse φ U (hφ U) ≫ M.val.map f := sorry

/-- Reverse a sectionwise bijective module-sheaf map by its explicit section fibers. -/
def inverseOfBijective
    (hφ : ∀ U : Cᵒᵖ, Function.Bijective (φ.val.app U).hom) : N ⟶ M where
  val :=
    { app := fun U ↦ sectionInverse φ U (hφ U)
      naturality := sectionInverse_naturality φ hφ }

@[simp]
theorem inverseOfBijective_app
    (hφ : ∀ U : Cᵒᵖ, Function.Bijective (φ.val.app U).hom) (U : Cᵒᵖ) (x : N.val.obj U) :
    ((inverseOfBijective φ hφ).val.app U).hom x = sectionPreimage φ U x := rfl

/-- The actual section preimage functions recover the source after the forward map. -/
theorem hom_inverseOfBijective
    (hφ : ∀ U : Cᵒᵖ, Function.Bijective (φ.val.app U).hom) :
    φ ≫ inverseOfBijective φ hφ = 𝟙 M := sorry

/-- The actual section preimage functions recover the target under bijectivity. -/
theorem inverseOfBijective_hom
    (hφ : ∀ U : Cᵒᵖ, Function.Bijective (φ.val.app U).hom) :
    inverseOfBijective φ hφ ≫ φ = 𝟙 N := sorry

/-- A module-sheaf isomorphism with explicit forward and reverse section functions. -/
def isoOfBijective
    (hφ : ∀ U : Cᵒᵖ, Function.Bijective (φ.val.app U).hom) : M ≅ N where
  hom := φ
  inv := inverseOfBijective φ hφ
  hom_inv_id := hom_inverseOfBijective φ hφ
  inv_hom_id := inverseOfBijective_hom φ hφ

end SheafOfModules
