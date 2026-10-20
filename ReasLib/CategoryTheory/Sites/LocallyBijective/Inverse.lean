/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Inverting locally bijective maps by descent

The reverse section function glues preimages on the specified image sieve.
Its local preimages are taken from membership in that sieve, rather than from
a global surjectivity certificate.  This exposes the descent construction used
inside Mathlib's locally bijective isomorphism criterion.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F G : Sheaf J (Type w)} (φ : F ⟶ G)
variable [IsLocallyInjective φ]

/-- The local preimages on the actual image sieve form a compatible family. -/
theorem localPreimage_compatible (U : Cᵒᵖ) (s : G.obj.obj U) :
    (Presieve.FamilyOfElements.localPreimage φ.hom s).Compatible := by
  intro Y₁ Y₂ W g₁ g₂ f₁ f₂ hf₁ hf₂ h
  apply ((isLocallyInjective_iff_injective φ).mp inferInstance) (op W)
  have e₁ := NatTrans.naturality_apply φ.hom g₁.op
    (Presheaf.localPreimage φ.hom s f₁ hf₁)
  have e₂ := NatTrans.naturality_apply φ.hom g₂.op
    (Presheaf.localPreimage φ.hom s f₂ hf₂)
  have e₃ := congr_arg (G.obj.map g₁.op)
    (Presheaf.app_localPreimage φ.hom s f₁ hf₁)
  have e₄ := congr_arg (G.obj.map g₂.op)
    (Presheaf.app_localPreimage φ.hom s f₂ hf₂)
  refine e₁.trans (e₃.trans (Eq.trans ?_ (e₄.symm.trans e₂.symm)))
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  simp only [← op_comp, h]

variable [IsLocallySurjective φ]

/-- Glue preimages on the specified image sieve using the source sheaf's descent. -/
def localInverseSection (U : Cᵒᵖ) (s : G.obj.obj U) : F.obj.obj U :=
  (((isSheaf_iff_isSheaf_of_type J F.obj).mp F.property) _
    (Presheaf.imageSieve_mem J φ.hom s)).amalgamate
      (Presieve.FamilyOfElements.localPreimage φ.hom s)
      (localPreimage_compatible φ U s)

/-- The glued section restricts to the chosen preimage on every image-sieve arrow. -/
theorem localInverseSection_restrict (U : Cᵒᵖ) (s : G.obj.obj U)
    {V : C} (g : V ⟶ U.unop) (hg : Presheaf.imageSieve φ.hom s g) :
    F.obj.map g.op (localInverseSection φ U s) =
      Presheaf.localPreimage φ.hom s g hg := by
  exact (((isSheaf_iff_isSheaf_of_type J F.obj).mp F.property) _
    (Presheaf.imageSieve_mem J φ.hom s)).valid_glue
      (localPreimage_compatible φ U s) g hg

/-- The reverse map has the explicit local-preimage-and-gluing section functions. -/
def localInverse : G ⟶ F where
  hom :=
    { app := fun U ↦ TypeCat.ofHom (localInverseSection φ U)
      naturality := sorry }

@[simp]
theorem localInverse_app (U : Cᵒᵖ) (s : G.obj.obj U) :
    (localInverse φ).hom.app U s = localInverseSection φ U s := rfl

/-- Local uniqueness makes descent independent of the local representative choices. -/
theorem hom_localInverse : φ ≫ localInverse φ = 𝟙 F := sorry

/-- The local image-sieve specification recovers the given section after descent. -/
theorem localInverse_hom : localInverse φ ≫ φ = 𝟙 G := sorry

/-- A locally bijective map with its explicitly constructed reverse by descent. -/
def isoOfLocallyBijective : F ≅ G where
  hom := φ
  inv := localInverse φ
  hom_inv_id := hom_localInverse φ
  inv_hom_id := localInverse_hom φ

end CategoryTheory.Sheaf
