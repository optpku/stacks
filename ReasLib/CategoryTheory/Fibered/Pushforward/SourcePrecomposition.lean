/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward
import Mathlib.Tactic.CrossRefAttribute

/-!
# Source precomposition for pushforward

For the prelocalized pushforward source `u ₚₚ p`, precomposing the comma arrow of an object
with a morphism in `D` gives a canonical lift for the source projection.  The construction is
independent of localization, a chosen cleavage, and any topology; later pushforward arguments
use it as their raw cartesian chart.
-/

@[expose] public section

universe uC uD uS vC vD vS

namespace CategoryTheory

open Limits
open scoped Functor

namespace Functor.Pushforward.Source

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-- Lemma 8.12.6 (tag 04WG): the source object obtained by precomposing the comma arrow of
`Y : u ₚₚ p` with `f : V ⟶ Y.fst.left`. -/
@[stacks 04WG "source precomposition object"]
def precomposeObj {u : C ⥤ D} {p : S ⥤ C} (Y : u ₚₚ p) {V : D}
    (f : V ⟶ Y.fst.left) : u ₚₚ p :=
  { fst :=
      { left := V
        right := Y.fst.right
        hom := f ≫ Y.fst.hom }
    snd := Y.snd
    iso := Y.iso }

namespace precomposeHom

/-- The comma-square condition for the canonical source precomposition lift. -/
@[stacks 04WG "source precomposition comma compatibility"]
theorem fst.naturality {u : C ⥤ D} {p : S ⥤ C} (Y : u ₚₚ p) {V : D}
    (f : V ⟶ Y.fst.left) :
    (𝟭 D).map f ≫ Y.fst.hom =
      (f ≫ Y.fst.hom) ≫ u.map (𝟙 Y.fst.right) := sorry

/-- The pullback compatibility condition for the canonical source precomposition lift. -/
@[stacks 04WG "source precomposition pullback compatibility"]
theorem compatibility {u : C ⥤ D} {p : S ⥤ C} (Y : u ₚₚ p) {V : D}
    (f : V ⟶ Y.fst.left) :
    𝟙 Y.fst.right ≫ Y.iso.hom =
      (precomposeObj Y f).iso.hom ≫ p.map (𝟙 Y.snd) := sorry

end precomposeHom

/-- Lemma 8.12.6 (tag 04WG): the canonical precomposition lift in the prelocalized
pushforward source. -/
@[stacks 04WG "source precomposition lift"]
def precomposeHom {u : C ⥤ D} {p : S ⥤ C} (Y : u ₚₚ p) {V : D}
    (f : V ⟶ Y.fst.left) : precomposeObj Y f ⟶ Y where
  fst :=
    { left := f
      right := 𝟙 Y.fst.right
      w := precomposeHom.fst.naturality Y f }
  snd := 𝟙 Y.snd
  w := precomposeHom.compatibility Y f

namespace precomposeFactor

/-- The comma-square condition for a factor through a source precomposition lift. -/
@[stacks 04WG "source precomposition factor comma compatibility"]
theorem fst.naturality {u : C ⥤ D} {p : S ⥤ C}
    {Y Z : u ₚₚ p} {V : D} (f : V ⟶ Y.fst.left)
    (g : Z.fst.left ⟶ V) (θ : Z ⟶ Y) (hθ : θ.fst.left = g ≫ f) :
    (𝟭 D).map g ≫ (f ≫ Y.fst.hom) = Z.fst.hom ≫ u.map θ.fst.right := sorry

/-- The pullback compatibility condition for a factor through a source precomposition lift. -/
@[stacks 04WG "source precomposition factor pullback compatibility"]
theorem compatibility {u : C ⥤ D} {p : S ⥤ C}
    {Y Z : u ₚₚ p} {V : D} (f : V ⟶ Y.fst.left) (θ : Z ⟶ Y) :
    θ.fst.right ≫ (precomposeObj Y f).iso.hom = Z.iso.hom ≫ p.map θ.snd := sorry

end precomposeFactor

/-- Lemma 8.12.6 (tag 04WG): the strict factor through a source precomposition lift. -/
@[stacks 04WG "source precomposition factor"]
def precomposeFactor {u : C ⥤ D} {p : S ⥤ C}
    {Y Z : u ₚₚ p} {V : D} (f : V ⟶ Y.fst.left)
    (g : Z.fst.left ⟶ V) (θ : Z ⟶ Y) (hθ : θ.fst.left = g ≫ f) :
    Z ⟶ precomposeObj Y f where
  fst :=
    { left := g
      right := θ.fst.right
      w := precomposeFactor.fst.naturality f g θ hθ }
  snd := θ.snd
  w := precomposeFactor.compatibility f θ

/-- Lemma 8.12.6 (tag 04WG): the canonical factor followed by the source precomposition lift
is the given morphism. -/
@[stacks 04WG "source precomposition factor composition"]
theorem precomposeFactor.comp {u : C ⥤ D} {p : S ⥤ C}
    {Y Z : u ₚₚ p} {V : D} (f : V ⟶ Y.fst.left)
    (g : Z.fst.left ⟶ V) (θ : Z ⟶ Y) (hθ : θ.fst.left = g ≫ f) :
    precomposeFactor f g θ hθ ≫ precomposeHom Y f = θ := sorry

/-- Lemma 8.12.6 (tag 04WG): precomposing the comma arrow with a morphism in `D` is a strongly
cartesian lift for the source projection of the pushforward. -/
@[stacks 04WG "source precomposition strongly cartesian lift"]
theorem precomposeHom.isStronglyCartesian
    {u : C ⥤ D} {p : S ⥤ C} (Y : u ₚₚ p) {V : D}
    (f : V ⟶ Y.fst.left) :
    (sourceProjection u p).IsStronglyCartesian f (precomposeHom Y f) := sorry

/-- Lemma 8.12.6 (tag 04WG): the source projection sends the canonical precomposition lift to
the morphism used to define it. -/
@[stacks 04WG "source precomposition projection map"]
theorem precomposeHom.sourceProjection.map
    {u : C ⥤ D} {p : S ⥤ C} (Y : u ₚₚ p) {V : D}
    (f : V ⟶ Y.fst.left) :
    (sourceProjection u p).map (precomposeHom Y f) = f := sorry

end Functor.Pushforward.Source

end CategoryTheory
