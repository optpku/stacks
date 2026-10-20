/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.Map
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {Y X T S : Scheme.{u}}

/-- A commutative square of schemes induces a morphism between geometric fibers. -/
def geometricFiberMap (i : Y ⟶ X) (g : Y ⟶ T)
    (f : X ⟶ S) (k : T ⟶ S) (sq : CommSq i g f k)
    (tbar : Scheme.GeometricPoint T) :
    pullback g tbar.hom ⟶ pullback f (tbar.map k).hom :=
  pullback.map g tbar.hom f (tbar.map k).hom i (𝟙 _) k sq.w.symm
    ((Scheme.GeometricPoint.map_hom tbar k).symm.trans
      (Category.id_comp (tbar.map k).hom).symm)

/-- The first projection of the induced geometric-fiber morphism postcomposes with
the top morphism of the square. -/
theorem geometricFiberMap_fst (i : Y ⟶ X) (g : Y ⟶ T)
    (f : X ⟶ S) (k : T ⟶ S) (sq : CommSq i g f k)
    (tbar : Scheme.GeometricPoint T) :
    geometricFiberMap i g f k sq tbar ≫ pullback.fst f (tbar.map k).hom =
      pullback.fst g tbar.hom ≫ i := sorry

/-- The second projection of the induced geometric-fiber morphism preserves the
geometric-point coordinate. -/
theorem geometricFiberMap_snd (i : Y ⟶ X) (g : Y ⟶ T)
    (f : X ⟶ S) (k : T ⟶ S) (sq : CommSq i g f k)
    (tbar : Scheme.GeometricPoint T) :
    geometricFiberMap i g f k sq tbar ≫ pullback.snd f (tbar.map k).hom =
      pullback.snd g tbar.hom := sorry

end AlgebraicGeometry.Scheme.Hom
