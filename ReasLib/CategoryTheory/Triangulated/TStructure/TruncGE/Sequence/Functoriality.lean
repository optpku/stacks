/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Triangulated.TStructure.TruncGE.Sequence

@[expose] public section

/-!
# Functoriality of Sequential Lower Truncations

This file packages an antitone lower-truncation sequence as a functor of the
object being truncated and exposes the componentwise computation API.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.Triangulated.TStructure.TruncGE.Sequence

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

noncomputable section

/-- Successor truncation comparisons are natural in the object being
truncated. -/
theorem map_naturality (t : TStructure C) {X Y : C} (f : X ⟶ Y)
    (p : ℕ → ℤ) (hp : Antitone p) (n : ℕ) :
    (ofAntitone t X p hp).stepMap n ≫ (t.truncGE (p n)).map f =
      (t.truncGE (p (n + 1))).map f ≫
        (ofAntitone t Y p hp).stepMap n := sorry

/-- A morphism induces the componentwise canonical morphism between its
antitone lower-truncation sequences. -/
@[stacks 0H72]
def map (t : TStructure C) {X Y : C} (f : X ⟶ Y)
    (p : ℕ → ℤ) (hp : Antitone p) :
    ofAntitone t X p hp ⟶ ofAntitone t Y p hp :=
  NatTrans.ofOpSequence (fun n ↦ (t.truncGE (p n)).map f)
    (map_naturality t f p hp)

/-- A component of the induced sequence morphism is the corresponding
lower-truncation map. -/
@[simp]
theorem map_app (t : TStructure C) {X Y : C} (f : X ⟶ Y)
    (p : ℕ → ℤ) (hp : Antitone p) (n : ℕ) :
    (map t f p hp).app (op n) = (t.truncGE (p n)).map f := sorry

/-- The sequence morphism induced by an identity is the identity. -/
@[simp]
theorem map_id (t : TStructure C) (X : C) (p : ℕ → ℤ)
    (hp : Antitone p) :
    map t (𝟙 X) p hp = 𝟙 (ofAntitone t X p hp) := sorry

/-- Morphisms of lower-truncation sequences preserve composition. -/
@[simp]
theorem map_comp (t : TStructure C) {X Y Z : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) (p : ℕ → ℤ) (hp : Antitone p) :
    map t (f ≫ g) p hp = map t f p hp ≫ map t g p hp := sorry

/-- Taking the antitone sequence of lower truncations is functorial in the
object being truncated. -/
@[stacks 0H72]
def functor (t : TStructure C) (p : ℕ → ℤ) (hp : Antitone p) :
    C ⥤ SequentialInverseSystem C where
  obj X := ofAntitone t X p hp
  map f := map t f p hp
  map_id X := map_id t X p hp
  map_comp f g := map_comp t f g p hp

/-- Evaluating the lower-truncation sequence functor gives the selected
antitone sequence. -/
@[simp]
theorem functor_obj (t : TStructure C) (X : C) (p : ℕ → ℤ)
    (hp : Antitone p) :
    (functor t p hp).obj X = ofAntitone t X p hp := sorry

/-- The map of the lower-truncation sequence functor is the canonical
componentwise truncation map. -/
@[simp]
theorem functor_map (t : TStructure C) {X Y : C} (f : X ⟶ Y)
    (p : ℕ → ℤ) (hp : Antitone p) :
    (functor t p hp).map f = map t f p hp := sorry

/-- A sequence morphism commutes with every transition map, expressed at
explicit truncation stages. -/
@[reassoc]
theorem transitionMap_comp_map_app (t : TStructure C) {X Y : C}
    (f : X ⟶ Y) (p : ℕ → ℤ) (hp : Antitone p)
    {m n : ℕ} (h : m ≤ n) :
    (ofAntitone t X p hp).transitionMap h ≫ (map t f p hp).app (op m) =
      (map t f p hp).app (op n) ≫
        (ofAntitone t Y p hp).transitionMap h := sorry

end

end CategoryTheory.Triangulated.TStructure.TruncGE.Sequence
