/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Bilinear.LocallyBijective
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Sheafification of tensor products of locally bijective maps

The inverse is constructed by bilinear local descent into the actual associated
sheaf and then by the existing ordinary sheafification adjunction.  This module
does not use a monoidal structure on sheaves of modules or assume an inverse to
the tensor map.  Its inverse laws are Prop proof debt.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v w

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Sheaf J CommRingCat.{w})
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]

local notation "a" =>
  (sheafification (R := Sheaf.ringSheafOfComm R) (𝟙 (ringPresheaf R.obj)))
local notation "adj" =>
  (sheafificationAdjunction (R := Sheaf.ringSheafOfComm R)
    (𝟙 (ringPresheaf R.obj)))

/-- The target sheaf condition is obtained from the actual associated sheaf,
including the identity restriction of scalars in the adjunction's right adjoint. -/
private theorem associatedTarget_isSheaf
    (P : PresheafOfModules.{w} (ringPresheaf R.obj)) :
    Presieve.IsSheaf J
      (((SheafOfModules.forget (Sheaf.ringSheafOfComm R) ⋙
          restrictScalars (𝟙 (ringPresheaf R.obj))).obj ((a).obj P)).presheaf ⋙
        forget AddCommGrpCat.{w}) := by
  change Presieve.IsSheaf J (((a).obj P).val.presheaf ⋙ forget AddCommGrpCat.{w})
  exact (isSheaf_iff_isSheaf_of_type J _).1
    (Presheaf.isSheaf_comp_of_isSheaf J _ (forget AddCommGrpCat.{w})
      ((a).obj P).isSheaf)

variable {F₁ F₂ G₁ G₂ : PresheafOfModules.{w} (ringPresheaf R.obj)}

/-- An actual inverse to the sheafified tensor map.  The two descents construct
a tensor morphism into the associated sheaf of the original tensor product;
the ordinary adjunction, whose data are already implemented, transposes it. -/
def tensorSheafificationInv
    (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂)
    [IsLocallyInjective J f] [IsLocallySurjective J f]
    [IsLocallyInjective J g] [IsLocallySurjective J g] :
    (a).obj (Monoidal.tensorObj F₂ G₂) ⟶ (a).obj (Monoidal.tensorObj F₁ G₁) :=
  ((adj).homEquiv (Monoidal.tensorObj F₂ G₂)
    ((a).obj (Monoidal.tensorObj F₁ G₁))).symm
      (BilinearMap.descendRight (J := J) g (by exact associatedTarget_isSheaf R _)
        (BilinearMap.descendLeft (J := J) f (by exact associatedTarget_isSheaf R _)
          (BilinearMap.ofHom ((adj).unit.app (Monoidal.tensorObj F₁ G₁))))).toHom

/-- On the source, the descended bilinear map agrees with the unit on pure
tensors.  Adjunction naturality and injectivity give this inverse law. -/
theorem tensorSheafification_hom_inv_id
    (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂)
    [IsLocallyInjective J f] [IsLocallySurjective J f]
    [IsLocallyInjective J g] [IsLocallySurjective J g] :
    (a).map (f ⊗ₘ g) ≫ tensorSheafificationInv R f g =
      𝟙 ((a).obj (Monoidal.tensorObj F₁ G₁)) := by
  sorry

/-- On the target, precompose with both locally bijective inputs and use the
two descent uniqueness statements, followed by adjunction injectivity. -/
theorem tensorSheafification_inv_hom_id
    (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂)
    [IsLocallyInjective J f] [IsLocallySurjective J f]
    [IsLocallyInjective J g] [IsLocallySurjective J g] :
    tensorSheafificationInv R f g ≫ (a).map (f ⊗ₘ g) =
      𝟙 ((a).obj (Monoidal.tensorObj F₂ G₂)) := by
  sorry

/-- Sheafification carries the tensor product of two locally bijective module
maps to an isomorphism, with the explicit inverse constructed above. -/
def tensorSheafificationIso
    (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂)
    [IsLocallyInjective J f] [IsLocallySurjective J f]
    [IsLocallyInjective J g] [IsLocallySurjective J g] :
    (a).obj (Monoidal.tensorObj F₁ G₁) ≅ (a).obj (Monoidal.tensorObj F₂ G₂) where
  hom := (a).map (f ⊗ₘ g)
  inv := tensorSheafificationInv R f g
  hom_inv_id := tensorSheafification_hom_inv_id R f g
  inv_hom_id := tensorSheafification_inv_hom_id R f g

end PresheafOfModules
