/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Comparison.Construction.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Relative inertia diagonal-comparison naturality

This leaf assembles the canonical object owner into a functor and a based functor.  Its private
map laws are construction obligations; the public `map.comm` and `map.naturality` equations are
the reusable naturality API for downstream pseudo-pullback arguments.
-/

open CategoryTheory
open CategoryTheory.Limits
open BasedCategory
open BasedFunctor
open scoped Bicategory

universe uC vC uS vS uS' vS'

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]
variable {S' : Type uS'} [Category.{vS'} S']
variable (F : S ⥤ S')
variable (p : S ⥤ C)
variable {p}
variable (p' : S' ⥤ C)

section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace RelativeInertia.Implementation

/-- The inertia comparison respects the stored isomorphisms in the outer pseudo-pullback. -/
private theorem Comparison.map_comm (comm : F ⋙ p' = p)
    {X Y : RelativeInertia F} (f : X ⟶ Y) :
    CommSq
      ((BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm)).map
        (RelativeInertia.hom f))
      (PseudoPullback.comparison
        (BasedFunctor.RelativeInertia.diagonalComparisonObj
          (BasedFunctor.ofFunctor F comm) X))
      (PseudoPullback.comparison
        (BasedFunctor.RelativeInertia.diagonalComparisonObj
          (BasedFunctor.ofFunctor F comm) Y))
      ((BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm)).map
        (RelativeInertia.hom f)) := sorry
/- Proof strategy: apply `PseudoPullback.hom_ext`; the first component is
`RelativeInertia.hom.naturality f` after reassociation and the second component is the identity law. -/

/-- The underlying relative-inertia arrow lies over its image in `C`. -/
private theorem Comparison.map_isHomLift (comm : F ⋙ p' = p)
    {X Y : RelativeInertia F} (f : X ⟶ Y) :
    p.IsHomLift (p.map (RelativeInertia.hom f)) (RelativeInertia.hom f) := sorry
/- Proof strategy: use the canonical `Functor.IsHomLift.map` instance. -/

/-- Morphism map of the comparison from relative inertia to the diagonal self-pullback. -/
private def Comparison.map (comm : F ⋙ p' = p)
    {X Y : RelativeInertia F} (f : X ⟶ Y) :
    BasedFunctor.RelativeInertia.diagonalComparisonObj
        (BasedFunctor.ofFunctor F comm) X ⟶
      BasedFunctor.RelativeInertia.diagonalComparisonObj
        (BasedFunctor.ofFunctor F comm) Y :=
  PseudoPullback.Hom.mk (p.map (RelativeInertia.hom f)) (RelativeInertia.hom f)
    (Comparison.map_isHomLift F p' comm f)
    (RelativeInertia.hom f) (Comparison.map_isHomLift F p' comm f)
    (Comparison.map_comm F p' comm f)

/-- The relative-inertia comparison preserves identities. -/
private theorem Comparison.map_id (comm : F ⋙ p' = p)
    (X : RelativeInertia F) :
    Comparison.map F p' comm (𝟙 X) =
      𝟙 (BasedFunctor.RelativeInertia.diagonalComparisonObj
        (BasedFunctor.ofFunctor F comm) X) := sorry
/- Proof strategy: apply `PseudoPullback.hom_ext`; both component equalities are identities. -/

/-- The relative-inertia comparison preserves composition. -/
private theorem Comparison.map_comp (comm : F ⋙ p' = p)
    {X Y Z : RelativeInertia F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Comparison.map F p' comm (f ≫ g) =
      Comparison.map F p' comm f ≫ Comparison.map F p' comm g := sorry
/- Proof strategy: apply `PseudoPullback.hom_ext`; both components reduce to composition in `S`. -/

/-- Underlying functor of the comparison from relative inertia to the diagonal self-pullback. -/
private def Comparison.functor (comm : F ⋙ p' = p) :
    RelativeInertia F ⥤
      (PseudoPullback (BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm))
        (BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm))).obj where
  obj := fun X ↦ BasedFunctor.RelativeInertia.diagonalComparisonObj
    (BasedFunctor.ofFunctor F comm) X
  map := Comparison.map F p' comm
  map_id := Comparison.map_id F p' comm
  map_comp := Comparison.map_comp F p' comm

/-- The relative-inertia comparison commutes strictly with projection to `C`. -/
private theorem Comparison.functor_comm (comm : F ⋙ p' = p) :
    Comparison.functor F p' comm ⋙
      (PseudoPullback (BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm))
        (BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm))).p =
      RelativeInertia.projection F p := sorry
/- Proof strategy: apply functor extensionality; object and morphism components retain exactly the
base object and base arrow stored by relative inertia. -/

/-- Bare-functor implementation of the inertia comparison; use
`BasedFunctor.RelativeInertia.diagonalComparison` on bundled input. -/
private def Comparison.toBasedFunctor (comm : F ⋙ p' = p) :
    BasedCategory.ofFunctor (RelativeInertia.projection F p) ⥤ᵇ
      PseudoPullback
        (BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm))
        (BasedFunctor.relativeDiagonal (BasedFunctor.ofFunctor F comm)) where
  toFunctor := Comparison.functor F p' comm
  w := Comparison.functor_comm F p' comm

end RelativeInertia.Implementation
end

namespace BasedFunctor

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable {X Y : BasedCategory C}

/-- The canonical comparison in `Cat/C` from relative inertia to the self-pullback of the relative
diagonal. -/
@[stacks 034H "relative-inertia diagonal comparison"]
def RelativeInertia.diagonalComparison (F : X ⥤ᵇ Y) :
    BasedCategory.ofFunctor (CategoryTheory.RelativeInertia.projection F.toFunctor X.p) ⥤ᵇ
      PseudoPullback (relativeDiagonal F) (relativeDiagonal F) :=
  CategoryTheory.RelativeInertia.Implementation.Comparison.toBasedFunctor F.toFunctor Y.p F.w

/-- The two relative-diagonal images of an inertia morphism form the comparison square stored by
the diagonal comparison. This is the direct specialization of `PseudoPullback.comm`. -/
@[stacks 034H "relative-inertia diagonal-comparison map square"]
theorem RelativeInertia.diagonalComparison.map.comm (F : X ⥤ᵇ Y)
    {A B : CategoryTheory.RelativeInertia F.toFunctor} (f : A ⟶ B) :
    CommSq
      ((relativeDiagonal F).map (CategoryTheory.RelativeInertia.hom f))
      (PseudoPullback.comparison ((RelativeInertia.diagonalComparison F).obj A))
      (PseudoPullback.comparison ((RelativeInertia.diagonalComparison F).obj B))
      ((relativeDiagonal F).map (CategoryTheory.RelativeInertia.hom f)) := sorry

/-- The stored comparison automorphisms commute with the relative-diagonal image of an inertia
morphism. This equation-oriented form is convenient for direct rewriting. -/
@[reassoc, stacks 034H "relative-inertia diagonal-comparison map naturality"]
theorem RelativeInertia.diagonalComparison.map.naturality (F : X ⥤ᵇ Y)
    {A B : CategoryTheory.RelativeInertia F.toFunctor} (f : A ⟶ B) :
    (relativeDiagonal F).map (CategoryTheory.RelativeInertia.hom f) ≫
        PseudoPullback.comparison ((RelativeInertia.diagonalComparison F).obj B) =
      PseudoPullback.comparison ((RelativeInertia.diagonalComparison F).obj A) ≫
        (relativeDiagonal F).map (CategoryTheory.RelativeInertia.hom f) := sorry

end BasedFunctor

end CategoryTheory
