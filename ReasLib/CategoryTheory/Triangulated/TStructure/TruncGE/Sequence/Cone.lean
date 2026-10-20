/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Triangulated.TStructure.TruncGE.Sequence.Functoriality

@[expose] public section

/-!
# Canonical Cones over Sequential Lower Truncations

The canonical projections `X ⟶ (t.truncGE (p n)).obj X` form a natural
transformation of inverse systems and hence a cone over the selected
lower-truncation sequence.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.Triangulated.TStructure.TruncGE.Sequence

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

noncomputable section

/-- The successor compatibility equation for the canonical maps from an
object to its selected lower truncations. -/
theorem πApp_naturality (t : TStructure C) (X : C) (p : ℕ → ℤ)
    (hp : Antitone p) (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj X).map
          (homOfLE (Nat.le_add_right n 1)).op ≫
        (t.truncGEπ (p n)).app X =
      (t.truncGEπ (p (n + 1))).app X ≫
        (ofAntitone t X p hp).stepMap n := sorry

/-- The canonical natural transformation from the constant inverse system at
an object to its selected lower-truncation sequence. -/
@[stacks 0H72]
def πApp (t : TStructure C) (X : C) (p : ℕ → ℤ)
    (hp : Antitone p) :
    (Functor.const ℕᵒᵖ).obj X ⟶ ofAntitone t X p hp :=
  NatTrans.ofOpSequence (fun n ↦ (t.truncGEπ (p n)).app X)
    (πApp_naturality t X p hp)

/-- The `n`th component of the canonical transformation is the lower
truncation projection at `p n`. -/
@[simp, stacks 0H72]
theorem πApp_app (t : TStructure C) (X : C) (p : ℕ → ℤ)
    (hp : Antitone p) (n : ℕ) :
    (πApp t X p hp).app (op n) = (t.truncGEπ (p n)).app X := sorry

/-- The canonical maps from an object to its lower truncations commute with
every transition, not only successor transitions. -/
@[reassoc (attr := simp)]
theorem πApp_comp_transitionMap (t : TStructure C) (X : C)
    (p : ℕ → ℤ) (hp : Antitone p) {m n : ℕ} (h : m ≤ n) :
    (πApp t X p hp).app (op n) ≫
        (ofAntitone t X p hp).transitionMap h =
      (πApp t X p hp).app (op m) := sorry

/-- The canonical transformations to lower-truncation sequences are natural
in the original object. -/
@[reassoc, stacks 0H72]
theorem π_naturality (t : TStructure C) {X Y : C} (f : X ⟶ Y)
    (p : ℕ → ℤ) (hp : Antitone p) :
    (Functor.const ℕᵒᵖ).map f ≫ πApp t Y p hp =
      πApp t X p hp ≫ map t f p hp := sorry

/-- The canonical maps to all selected lower truncations, natural in the
input object. -/
@[stacks 0H72]
def π (t : TStructure C) (p : ℕ → ℤ) (hp : Antitone p) :
    Functor.const ℕᵒᵖ ⟶ functor t p hp where
  app X := πApp t X p hp
  naturality _ _ f := π_naturality t f p hp

/-- Evaluating the global canonical transformation at an object gives its
canonical transformation of inverse systems. -/
@[simp, stacks 0H72]
theorem π_app (t : TStructure C) (X : C) (p : ℕ → ℤ)
    (hp : Antitone p) :
    (π t p hp).app X = πApp t X p hp := sorry

/-- A component of the global canonical transformation is the corresponding
lower-truncation projection. -/
@[simp, stacks 0H72]
theorem π_app_app (t : TStructure C) (X : C) (p : ℕ → ℤ)
    (hp : Antitone p) (n : ℕ) :
    ((π t p hp).app X).app (op n) = (t.truncGEπ (p n)).app X := sorry

/-- The canonical cone from an object to its selected lower-truncation
inverse system. -/
@[stacks 0H72]
def cone (t : TStructure C) (X : C) (p : ℕ → ℤ)
    (hp : Antitone p) : Cone (ofAntitone t X p hp) :=
  Cone.mk X (πApp t X p hp)

/-- The point of the canonical lower-truncation cone is the original object. -/
@[simp, stacks 0H72]
theorem cone_pt (t : TStructure C) (X : C) (p : ℕ → ℤ)
    (hp : Antitone p) :
    (cone t X p hp).pt = X := sorry

/-- A leg of the canonical cone is the corresponding lower-truncation
projection. -/
@[simp, stacks 0H72]
theorem cone_π_app (t : TStructure C) (X : C) (p : ℕ → ℤ)
    (hp : Antitone p) (n : ℕ) :
    (cone t X p hp).π.app (op n) = (t.truncGEπ (p n)).app X := sorry

/-- The compatibility equation defining the canonical morphism between
lower-truncation cones. -/
@[reassoc, stacks 0H72]
theorem coneMap_w (t : TStructure C) {X Y : C} (f : X ⟶ Y)
    (p : ℕ → ℤ) (hp : Antitone p) (n : ℕ) :
    f ≫ (cone t Y p hp).π.app (op n) =
      (cone t X p hp).π.app (op n) ≫ (map t f p hp).app (op n) := sorry

/-- A morphism induces the canonical morphism from the postcomposed source
cone to the target lower-truncation cone. -/
@[stacks 0H72]
def coneMap (t : TStructure C) {X Y : C} (f : X ⟶ Y)
    (p : ℕ → ℤ) (hp : Antitone p) :
    (Cone.postcompose (map t f p hp)).obj (cone t X p hp) ⟶
      cone t Y p hp where
  hom := f
  w j := coneMap_w t f p hp j.unop

/-- The apex map of the canonical cone morphism is the original morphism. -/
@[simp, stacks 0H72]
theorem coneMap_hom (t : TStructure C) {X Y : C} (f : X ⟶ Y)
    (p : ℕ → ℤ) (hp : Antitone p) :
    (coneMap t f p hp).hom = f := sorry

end

end CategoryTheory.Triangulated.TStructure.TruncGE.Sequence
