module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.TensorHom

@[expose] public section

/-!
# Split coequalizers of right-tensored character modules

Tensor–Hom duality transports morphisms and split coequalizers of character
modules after tensoring their underlying modules on the right.
-/

open CategoryTheory
open scoped MonoidalCategory

universe u

namespace CharacterModule.TensorHom

variable (R : Type u) [CommRing R]

/-- The tensor–character adjunction, with the fixed module in the right tensor factor. -/
noncomputable def rightIso (M Q : ModuleCat.{u} R) :
    CharacterModule.moduleObj R (M ⊗ Q) ≅
      ModuleCat.of R (Q ⟶ CharacterModule.moduleObj R M) :=
  (CharacterModule.functor R).mapIso (β_ Q M).op ≪≫
    appIso R (Opposite.op (Q, M))

/-- The forward map of `rightIso` curries a character after exchanging the tensor factors. -/
theorem rightIso_hom_apply (M Q : ModuleCat.{u} R)
    (χ : CharacterModule (TensorProduct R M Q)) (m : M) (q : Q) :
    (rightIso R M Q).hom χ q m = χ (m ⊗ₜ[R] q) := sorry

/-- The map on right-tensored character modules induced by a map of character modules. -/
noncomputable def rightMap {M N : ModuleCat.{u} R} (Q : ModuleCat.{u} R)
    (f : CharacterModule.moduleObj R M ⟶ CharacterModule.moduleObj R N) :
    CharacterModule.moduleObj R (M ⊗ Q) ⟶
      CharacterModule.moduleObj R (N ⊗ Q) :=
  (rightIso R M Q).hom ≫
    ((linearCoyoneda R (ModuleCat.{u} R)).obj (Opposite.op Q)).map f ≫
      (rightIso R N Q).inv

/-- The map `rightMap` sends an identity map to an identity map. -/
theorem rightMap_id (M Q : ModuleCat.{u} R) :
    rightMap R Q (𝟙 (CharacterModule.moduleObj R M)) =
      𝟙 (CharacterModule.moduleObj R (M ⊗ Q)) := sorry

/-- The map `rightMap` preserves composition. -/
theorem rightMap_comp {M N P : ModuleCat.{u} R} (Q : ModuleCat.{u} R)
    (f : CharacterModule.moduleObj R M ⟶ CharacterModule.moduleObj R N)
    (g : CharacterModule.moduleObj R N ⟶ CharacterModule.moduleObj R P) :
    rightMap R Q (f ≫ g) = rightMap R Q f ≫ rightMap R Q g := sorry

/-- The images under `rightMap` of the parallel maps still coequalize. -/
theorem rightMap_condition {M N P : ModuleCat.{u} R} (Q : ModuleCat.{u} R)
    {f g : CharacterModule.moduleObj R M ⟶ CharacterModule.moduleObj R N}
    {π : CharacterModule.moduleObj R N ⟶ CharacterModule.moduleObj R P}
    (q : IsSplitCoequalizer f g π) :
    rightMap R Q f ≫ rightMap R Q π =
      rightMap R Q g ≫ rightMap R Q π := sorry

/-- Applying `rightMap` to the right section preserves its splitting equation. -/
theorem rightMap_rightSection_π {M N P : ModuleCat.{u} R} (Q : ModuleCat.{u} R)
    {f g : CharacterModule.moduleObj R M ⟶ CharacterModule.moduleObj R N}
    {π : CharacterModule.moduleObj R N ⟶ CharacterModule.moduleObj R P}
    (q : IsSplitCoequalizer f g π) :
    rightMap R Q q.rightSection ≫ rightMap R Q π =
      𝟙 (CharacterModule.moduleObj R (P ⊗ Q)) := sorry

/-- Applying `rightMap` to the left section preserves its lower splitting equation. -/
theorem rightMap_leftSection_bottom {M N P : ModuleCat.{u} R} (Q : ModuleCat.{u} R)
    {f g : CharacterModule.moduleObj R M ⟶ CharacterModule.moduleObj R N}
    {π : CharacterModule.moduleObj R N ⟶ CharacterModule.moduleObj R P}
    (q : IsSplitCoequalizer f g π) :
    rightMap R Q q.leftSection ≫ rightMap R Q g =
      𝟙 (CharacterModule.moduleObj R (N ⊗ Q)) := sorry

/-- Applying `rightMap` to the left section preserves its upper splitting equation. -/
theorem rightMap_leftSection_top {M N P : ModuleCat.{u} R} (Q : ModuleCat.{u} R)
    {f g : CharacterModule.moduleObj R M ⟶ CharacterModule.moduleObj R N}
    {π : CharacterModule.moduleObj R N ⟶ CharacterModule.moduleObj R P}
    (q : IsSplitCoequalizer f g π) :
    rightMap R Q q.leftSection ≫ rightMap R Q f =
      rightMap R Q π ≫ rightMap R Q q.rightSection := sorry

/-- Tensoring the arguments of a split coequalizer of character modules on the
right by any module again gives a split coequalizer. -/
noncomputable def mapIsSplitCoequalizer {M N P : ModuleCat.{u} R}
    (Q : ModuleCat.{u} R)
    {f g : CharacterModule.moduleObj R M ⟶ CharacterModule.moduleObj R N}
    {π : CharacterModule.moduleObj R N ⟶ CharacterModule.moduleObj R P}
    (q : IsSplitCoequalizer f g π) :
    IsSplitCoequalizer (rightMap R Q f) (rightMap R Q g) (rightMap R Q π) where
  rightSection := rightMap R Q q.rightSection
  leftSection := rightMap R Q q.leftSection
  condition := rightMap_condition R Q q
  rightSection_π := rightMap_rightSection_π R Q q
  leftSection_bottom := rightMap_leftSection_bottom R Q q
  leftSection_top := rightMap_leftSection_top R Q q

/-- The transported split coequalizer uses the image of the original right section. -/
theorem mapIsSplitCoequalizer_rightSection {M N P : ModuleCat.{u} R}
    (Q : ModuleCat.{u} R)
    {f g : CharacterModule.moduleObj R M ⟶ CharacterModule.moduleObj R N}
    {π : CharacterModule.moduleObj R N ⟶ CharacterModule.moduleObj R P}
    (q : IsSplitCoequalizer f g π) :
    (mapIsSplitCoequalizer R Q q).rightSection = rightMap R Q q.rightSection := sorry

/-- The transported split coequalizer uses the image of the original left section. -/
theorem mapIsSplitCoequalizer_leftSection {M N P : ModuleCat.{u} R}
    (Q : ModuleCat.{u} R)
    {f g : CharacterModule.moduleObj R M ⟶ CharacterModule.moduleObj R N}
    {π : CharacterModule.moduleObj R N ⟶ CharacterModule.moduleObj R P}
    (q : IsSplitCoequalizer f g π) :
    (mapIsSplitCoequalizer R Q q).leftSection = rightMap R Q q.leftSection := sorry

end CharacterModule.TensorHom
