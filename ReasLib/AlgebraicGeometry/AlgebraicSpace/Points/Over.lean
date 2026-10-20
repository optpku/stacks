/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-!
# Schemes over a base and their Yoneda maps
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism `(Over.map U.hom).obj V ⟶ U` induced by the structure map of `V`. -/
def overMapHom {S : Scheme.{u}} {U : Over S} (V : Over U.left) :
    (Over.map U.hom).obj V ⟶ U :=
  Over.homMk V.hom rfl

/-- `overMapHom V` is `Over.homMk` of the structure morphism of `V`. -/
theorem overMapHom_eq {S : Scheme.{u}} {U : Over S} (V : Over U.left) :
    overMapHom V = Over.homMk V.hom rfl := rfl

/-- Yoneda of an identity morphism of schemes over `S` is the identity. -/
theorem ofOverMap_id {S : Scheme.{u}} (U : Over S) :
    ofOverMap (𝟙 U) = 𝟙 (ofOver U) := yoneda.map_id U

/-- Yoneda of a composite morphism of schemes over `S` is the composite. -/
theorem ofOverMap_comp {S : Scheme.{u}} {U U' U'' : Over S} (f : U ⟶ U') (g : U' ⟶ U'') :
    ofOverMap (f ≫ g) = ofOverMap f ≫ ofOverMap g := yoneda.map_comp f g

/-- Composing `V → U → S` or `V → U → U' → S` yields the same object of `Over S`. -/
def baseOverIso {S : Scheme.{u}} {U U' : Over S} (f : U ⟶ U') (V : Over U.left) :
    (Over.map U.hom).obj V ≅ (Over.map U'.hom).obj ((Over.map f.left).obj V) :=
  Over.isoMk (Iso.refl _)
    ((Category.id_comp _).trans
      ((Category.assoc V.hom f.left U'.hom).trans
        (congrArg (fun t ↦ V.hom ≫ t) (Over.w f))))

end AlgebraicGeometry.AlgebraicSpace
