module

public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Left Kan extensions along left adjoints

Left Kan extension along a left adjoint is computed by precomposition with its right adjoint.
Consequently, postcomposition by any coefficient functor preserves such Kan extensions.  This
file exposes that fact as a global instance so coefficient-change comparisons do not need local
instance reconstruction.
-/

@[expose] public section

open CategoryTheory

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]

/-- Every functor has a left Kan extension along a left adjoint. -/
instance hasLeftKanExtension_of_isLeftAdjoint
    (L : A ⥤ C) [L.IsLeftAdjoint] (F : A ⥤ B) :
    L.HasLeftKanExtension F :=
  (mkInitialOfLeftAdjoint _ ((Adjunction.ofIsLeftAdjoint L).whiskerLeft B) F).hasInitial

/-- Every coefficient functor preserves left Kan extensions along a left adjoint. -/
instance preservesLeftKanExtensions_of_isLeftAdjoint
    (L : A ⥤ C) [L.IsLeftAdjoint] (G : B ⥤ D) :
    G.PreservesLeftKanExtensions L := sorry

end CategoryTheory.Functor

-- These instances contain only universal-property proofs; they own no Kan-extension data.
