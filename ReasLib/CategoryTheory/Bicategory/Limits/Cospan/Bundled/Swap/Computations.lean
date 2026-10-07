module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Swap.Construction
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Swap.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for swapping bundled bicategorical cospans

This file exposes the generator-level action and involutivity of `Cospan.swap`. The bridge
statements to `CospanTransform.swap` and `CospanTransform.Hom.swap` keep downstream arguments
at the raw walking-cospan layer when that is more convenient.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory.Bicategory.Cospan

variable {B : Type u} [Bicategory.{w, v} B]

namespace swap

/-- Swapping a bundled cospan exchanges its left endpoint with its right endpoint. -/
@[simp]
theorem obj.left (S : Cospan B) :
    ((Cospan.swap B).obj S).left = S.right := sorry

/-- Swapping a bundled cospan exchanges its right endpoint with its left endpoint. -/
@[simp]
theorem obj.right (S : Cospan B) :
    ((Cospan.swap B).obj S).right = S.left := sorry

/-- Swapping a bundled cospan preserves its common target. -/
@[simp]
theorem obj.base (S : Cospan B) :
    ((Cospan.swap B).obj S).base = S.base := sorry

/-- The left leg of a swapped bundled cospan is its original right leg. -/
@[simp]
theorem obj.fst (S : Cospan B) :
    ((Cospan.swap B).obj S).fst = S.snd := sorry

/-- The right leg of a swapped bundled cospan is its original left leg. -/
@[simp]
theorem obj.snd (S : Cospan B) :
    ((Cospan.swap B).obj S).snd = S.fst := sorry

/-- Forgetting the bundled wrapper after swapping a cospan morphism gives the raw swapped
cospan transformation. -/
@[simp]
theorem map.toCospanTransform
    {S T : Cospan B} (ψ : S ⟶ T) :
    Hom.toCospanTransform ((Cospan.swap B).map ψ) =
      CospanTransform.swap (Hom.toCospanTransform ψ) := sorry

/-- Swapping a bundled-cospan morphism exchanges its left component with its right
component. -/
@[simp]
theorem map.left {S T : Cospan B} (ψ : S ⟶ T) :
    Hom.left ((Cospan.swap B).map ψ) = Hom.right ψ := sorry

/-- Swapping a bundled-cospan morphism exchanges its right component with its left
component. -/
@[simp]
theorem map.right {S T : Cospan B} (ψ : S ⟶ T) :
    Hom.right ((Cospan.swap B).map ψ) = Hom.left ψ := sorry

/-- Swapping a bundled-cospan morphism preserves its common-target component. -/
@[simp]
theorem map.base {S T : Cospan B} (ψ : S ⟶ T) :
    Hom.base ((Cospan.swap B).map ψ) = Hom.base ψ := sorry

/-- The left comparison of a swapped bundled-cospan morphism is its original right
comparison. -/
@[simp]
theorem map.leftIso {S T : Cospan B} (ψ : S ⟶ T) :
    Hom.leftIso ((Cospan.swap B).map ψ) = Hom.rightIso ψ := sorry

/-- The right comparison of a swapped bundled-cospan morphism is its original left
comparison. -/
@[simp]
theorem map.rightIso {S T : Cospan B} (ψ : S ⟶ T) :
    Hom.rightIso ((Cospan.swap B).map ψ) = Hom.leftIso ψ := sorry

/-- Forgetting the bundled wrapper after swapping a `2`-morphism gives the raw swapped
cospan modification. -/
@[simp]
theorem map₂.toModification
    {S T : Cospan B} {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    Hom₂.toModification ((Cospan.swap B).map₂ Γ) =
      CospanTransform.Hom.swap (Hom₂.toModification Γ) := sorry

/-- Swapping a bundled-cospan `2`-morphism exchanges its left cell with its right cell. -/
@[simp]
theorem map₂.left
    {S T : Cospan B} {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    Hom₂.left ((Cospan.swap B).map₂ Γ) = Hom₂.right Γ := sorry

/-- Swapping a bundled-cospan `2`-morphism exchanges its right cell with its left cell. -/
@[simp]
theorem map₂.right
    {S T : Cospan B} {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    Hom₂.right ((Cospan.swap B).map₂ Γ) = Hom₂.left Γ := sorry

/-- Swapping a bundled-cospan `2`-morphism preserves its common-target cell. -/
@[simp]
theorem map₂.base
    {S T : Cospan B} {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    Hom₂.base ((Cospan.swap B).map₂ Γ) = Hom₂.base Γ := sorry

/-- Bundled cospan swap preserves identity `1`-morphisms strictly. -/
@[simp]
theorem map.id (S : Cospan B) :
    (Cospan.swap B).map (𝟙 S) = 𝟙 ((Cospan.swap B).obj S) := sorry

/-- Bundled cospan swap preserves composition of `1`-morphisms strictly. -/
@[simp]
theorem map.comp {R S T : Cospan B} (ψ : R ⟶ S) (φ : S ⟶ T) :
    (Cospan.swap B).map (ψ ≫ φ) =
      (Cospan.swap B).map ψ ≫ (Cospan.swap B).map φ := sorry

/-- The identity comparison of bundled cospan swap is the equality isomorphism supplied by
its strict object. -/
theorem mapId.eqToIso (S : Cospan B) :
    (Cospan.swap B).mapId S = eqToIso ((Cospan.swap B).map_id S) := sorry

/-- The composition comparison of bundled cospan swap is the equality isomorphism supplied
by its strict object. -/
theorem mapComp.eqToIso
    {R S T : Cospan B} (ψ : R ⟶ S) (φ : S ⟶ T) :
    (Cospan.swap B).mapComp ψ φ =
      eqToIso ((Cospan.swap B).map_comp ψ φ) := sorry

/-- Swapping the endpoints and legs of a bundled cospan twice recovers the original
cospan. -/
@[simp, stacks 0040 "involutivity of bundled bicategorical cospan swap"]
theorem obj.involution (S : Cospan B) :
    (Cospan.swap B).obj ((Cospan.swap B).obj S) = S := sorry

/-- Swapping a bundled-cospan morphism twice recovers the original morphism. -/
@[simp]
theorem map.involution {S T : Cospan B} (ψ : S ⟶ T) :
    (Cospan.swap B).map ((Cospan.swap B).map ψ) = ψ := sorry

/-- After the canonical endpoint transports, swapping a bundled-cospan `2`-morphism twice
recovers the original `2`-morphism. -/
@[simp]
theorem map₂.involution
    {S T : Cospan B} {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    eqToHom (map.involution ψ).symm ≫
        (Cospan.swap B).map₂ ((Cospan.swap B).map₂ Γ) ≫
      eqToHom (map.involution φ) = Γ := sorry

end swap

/- This module introduces no data-bearing declaration. Its statements expose the direct
field swap, the strict comparison isomorphisms, and the canonical transports required by
involutivity on `2`-morphisms. -/

end CategoryTheory.Bicategory.Cospan
