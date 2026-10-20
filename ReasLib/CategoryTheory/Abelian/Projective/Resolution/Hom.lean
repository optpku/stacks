/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Morphisms of projective resolutions

Identity and composition retain the specified augmentation morphism. The chosen lift is
Mathlib's projective-resolution chain map, bundled with its augmentation compatibility.
These operations apply to arbitrary projective resolutions, independently of module freeness.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.ProjectiveResolution.Hom

variable {C : Type u} [Category.{v} C]

section

variable [HasZeroObject C] [HasZeroMorphisms C]
variable {X Y Z : C} {P : ProjectiveResolution X} {Q : ProjectiveResolution Y}
  {T : ProjectiveResolution Z} {f : X ⟶ Y} {g : Y ⟶ Z}

/-- The identity morphism of a projective resolution covers the identity augmentation map. -/
def id (P : ProjectiveResolution X) : Hom P P (𝟙 X) where
  hom := 𝟙 P.complex
  hom_f_zero_comp_π_f_zero := sorry

/-- Composition of compatible resolution morphisms covers the composite augmentation map. -/
def comp (φ : Hom P Q f) (ψ : Hom Q T g) : Hom P T (f ≫ g) where
  hom := φ.hom ≫ ψ.hom
  hom_f_zero_comp_π_f_zero := sorry

/-- The chain map underlying the identity resolution morphism is the identity. -/
@[simp]
theorem id_hom (P : ProjectiveResolution X) : (id P).hom = 𝟙 P.complex := rfl

/-- The chain map underlying composition is the composite of the underlying chain maps. -/
@[simp]
theorem comp_hom (φ : Hom P Q f) (ψ : Hom Q T g) :
    (comp φ ψ).hom = φ.hom ≫ ψ.hom := rfl

/-- A compatible resolution morphism is determined by its chain map. -/
@[ext]
theorem hom_ext {φ ψ : Hom P Q f} (h : φ.hom = ψ.hom) : φ = ψ := sorry

end

section

variable [Abelian C] {X Y : C}

/-- Bundle Mathlib's chosen chain-map lift with its augmentation compatibility. -/
def lift (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y) :
    Hom P Q f where
  hom := ProjectiveResolution.lift f P Q
  hom_f_zero_comp_π_f_zero := sorry

/-- The chain map underlying the bundled lift is Mathlib's projective-resolution lift. -/
@[simp]
theorem lift_hom (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y) :
    (lift f P Q).hom = ProjectiveResolution.lift f P Q := rfl

end

end CategoryTheory.ProjectiveResolution.Hom
