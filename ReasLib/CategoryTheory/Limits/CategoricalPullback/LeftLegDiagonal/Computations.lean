/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.LeftLegDiagonal.Basic

/-!
# Computations for left-leg diagonal squares

Projection, object, morphism, comparison-isomorphism, and square readouts for the ordinary
left-leg diagonal construction.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory.Limits

universe vU vX vV vY uU uX uV uY

namespace CategoricalPullback.CatCommSqOver.LeftLegDiagonal

variable {U : Type uU} [Category.{vU} U]
variable {X : Type uX} [Category.{vX} X]
variable {V : Type uV} [Category.{vV} V]
variable {Y : Type uY} [Category.{vY} Y]
variable {F : X ⥤ Y} {G : V ⥤ Y}

namespace map

/-- The forward component of the first-projection comparison for the left-leg map is the
identity. -/
@[simp]
theorem fstIso.hom.app (P : CatCommSqOver F G U) (z : P.snd ⊡ P.snd) :
    (fstIso P).hom.app z = 𝟙 _ := sorry

/-- The inverse component of the first-projection comparison for the left-leg map is the
identity. -/
@[simp]
theorem fstIso.inv.app (P : CatCommSqOver F G U) (z : P.snd ⊡ P.snd) :
    (fstIso P).inv.app z = 𝟙 _ := sorry

/-- The forward component of the second-projection comparison for the left-leg map is the
identity. -/
@[simp]
theorem sndIso.hom.app (P : CatCommSqOver F G U) (z : P.snd ⊡ P.snd) :
    (sndIso P).hom.app z = 𝟙 _ := sorry

/-- The inverse component of the second-projection comparison for the left-leg map is the
identity. -/
@[simp]
theorem sndIso.inv.app (P : CatCommSqOver F G U) (z : P.snd ⊡ P.snd) :
    (sndIso P).inv.app z = 𝟙 _ := sorry

/-- The first object component of the map induced by the left leg is `P.fst`. -/
@[simp]
theorem obj.fst (P : CatCommSqOver F G U) (z : P.snd ⊡ P.snd) :
    ((LeftLegDiagonal.map P).obj z).fst = P.fst.obj z.fst := sorry

/-- The second object component of the map induced by the left leg is `P.fst`. -/
@[simp]
theorem obj.snd (P : CatCommSqOver F G U) (z : P.snd ⊡ P.snd) :
    ((LeftLegDiagonal.map P).obj z).snd = P.fst.obj z.snd := sorry

/-- The structural isomorphism transported by the left-leg map is obtained by conjugating
`G.mapIso z.iso` with the two components of `P.iso`. -/
@[simp]
theorem obj.iso (P : CatCommSqOver F G U) (z : P.snd ⊡ P.snd) :
    ((LeftLegDiagonal.map P).obj z).iso =
      P.iso.app z.fst ≪≫ G.mapIso z.iso ≪≫ P.iso.symm.app z.snd := sorry

/-- The first morphism component of the map induced by the left leg is `P.fst.map`. -/
@[simp]
theorem hom.fst (P : CatCommSqOver F G U)
    {z z' : P.snd ⊡ P.snd} (f : z ⟶ z') :
    ((LeftLegDiagonal.map P).map f).fst = P.fst.map f.fst := sorry

/-- The second morphism component of the map induced by the left leg is `P.fst.map`. -/
@[simp]
theorem hom.snd (P : CatCommSqOver F G U)
    {z z' : P.snd ⊡ P.snd} (f : z ⟶ z') :
    ((LeftLegDiagonal.map P).map f).snd = P.fst.map f.snd := sorry

end map

namespace iso

/-- The first projection of the forward diagonal comparison is the canonical first-projection
comparison for the left-leg map. -/
@[simp]
theorem hom.app.fst (P : CatCommSqOver F G U) (x : U) :
    ((LeftLegDiagonal.iso P).hom.app x).fst =
      (map.fstIso P).hom.app ((Δₚ P.snd).obj x) := sorry

/-- The second projection of the forward diagonal comparison is the canonical second-projection
comparison for the left-leg map. -/
@[simp]
theorem hom.app.snd (P : CatCommSqOver F G U) (x : U) :
    ((LeftLegDiagonal.iso P).hom.app x).snd =
      (map.sndIso P).hom.app ((Δₚ P.snd).obj x) := sorry

/-- The first projection of the inverse diagonal comparison is the inverse canonical
first-projection comparison for the left-leg map. -/
@[simp]
theorem inv.app.fst (P : CatCommSqOver F G U) (x : U) :
    ((LeftLegDiagonal.iso P).inv.app x).fst =
      (map.fstIso P).inv.app ((Δₚ P.snd).obj x) := sorry

/-- The second projection of the inverse diagonal comparison is the inverse canonical
second-projection comparison for the left-leg map. -/
@[simp]
theorem inv.app.snd (P : CatCommSqOver F G U) (x : U) :
    ((LeftLegDiagonal.iso P).inv.app x).snd =
      (map.sndIso P).inv.app ((Δₚ P.snd).obj x) := sorry

end iso

namespace square

/-- The top leg of the left-leg diagonal square is the relative diagonal of `P.snd`. -/
@[simp]
theorem fst (P : CatCommSqOver F G U) :
    (LeftLegDiagonal.square P).fst = Δₚ P.snd := sorry

/-- The left leg of the left-leg diagonal square is the original functor `P.fst`. -/
@[simp]
theorem snd (P : CatCommSqOver F G U) :
    (LeftLegDiagonal.square P).snd = P.fst := sorry

/-- The structural isomorphism of the left-leg diagonal square is the canonical diagonal
comparison. -/
@[simp]
theorem iso (P : CatCommSqOver F G U) :
    (LeftLegDiagonal.square P).iso = LeftLegDiagonal.iso P := sorry

end square

end CategoricalPullback.CatCommSqOver.LeftLegDiagonal

end CategoryTheory.Limits
