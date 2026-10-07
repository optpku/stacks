module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Kernel-cotangent module presheaves

A morphism of presheaves of commutative rings determines the presheaf whose value is the
cotangent module `ker(f) / ker(f) ^ 2`. This file owns that construction independently of any
topology, sheafification, or chosen presentation.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe c v w

namespace PresheafOfModules.KernelCotangent

variable {C : Type c} [Category.{v} C]
variable {R S : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- The objectwise kernel ideal of a morphism of commutative-ring presheaves. -/
abbrev ideal (f : R ⟶ S) (U : Cᵒᵖ) : Ideal (R.obj U) :=
  RingHom.ker ((f.app U).hom)

/-- The objectwise kernel-cotangent module `ker(f_U) / ker(f_U) ^ 2`. -/
abbrev obj (f : R ⟶ S) (U : Cᵒᵖ) : ModuleCat (R.obj U) :=
  ModuleCat.of (R.obj U) (ideal f U).Cotangent

/-- Restriction along a presheaf morphism sends the source kernel ideal into the pullback of the
target kernel ideal. -/
theorem ideal_le_comap (f : R ⟶ S) {U V : Cᵒᵖ} (i : U ⟶ V) :
    ideal f U ≤ (ideal f V).comap ((R.map i).hom) := sorry

/-- The restriction morphism on objectwise kernel-cotangent modules. -/
abbrev map (f : R ⟶ S) {U V : Cᵒᵖ} (i : U ⟶ V) :
    obj f U ⟶
      (ModuleCat.restrictScalars ((R.map i).hom)).obj (obj f V) :=
  ConcreteCategory.ofHom (C := ModuleCat (R.obj U))
    (@Ideal.mapCotangent
      (R.obj U) _ (R.obj U) (R.obj V) _ _
      (Algebra.id (R.obj U)) ((R.map i).hom.toAlgebra)
      (ideal f U) (ideal f V)
      (@Algebra.ofId (R.obj U) (R.obj V) _ _ ((R.map i).hom.toAlgebra))
      (ideal_le_comap f i))

/-- Restriction sends a kernel-cotangent generator to the generator represented by its image. -/
theorem map_toCotangent (f : R ⟶ S) {U V : Cᵒᵖ} (i : U ⟶ V)
    (x : ideal f U) :
    map f i ((ideal f U).toCotangent x) =
      (ideal f V).toCotangent ⟨(R.map i).hom x, ideal_le_comap f i x.2⟩ := sorry

/-- Identity restriction acts trivially on an objectwise kernel-cotangent module. -/
theorem map_id (f : R ⟶ S) (U : Cᵒᵖ) :
    map f (𝟙 U) =
      (ModuleCat.restrictScalarsId'
        ((R.map (𝟙 U)).hom) (congrArg CommRingCat.Hom.hom (R.map_id U))).inv.app _ := sorry

/-- Kernel-cotangent restriction morphisms compose functorially. -/
theorem map_comp (f : R ⟶ S) {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    map f (i ≫ j) =
      map f i ≫ (ModuleCat.restrictScalars ((R.map i).hom)).map (map f j) ≫
        (ModuleCat.restrictScalarsComp'
          ((R.map i).hom) ((R.map j).hom) ((R.map (i ≫ j)).hom)
          (congrArg CommRingCat.Hom.hom (R.map_comp i j))).inv.app _ := sorry

/-- The presheaf of kernel-cotangent modules attached to a morphism of commutative-ring
presheaves. -/
@[stacks 08TF "kernel-cotangent presheaf", stacks 08TS "kernel-cotangent presheaf"]
def presheaf (f : R ⟶ S) :
    PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat.{w}) where
  obj := obj f
  map := map f
  map_id := map_id f
  map_comp := map_comp f

end PresheafOfModules.KernelCotangent
