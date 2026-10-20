/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.BaseProjection
public import ReasLib.CategoryTheory.Fibered.Groupoids.BaseProjection.Naturality
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoryTheory.TwoFibreProduct

namespace AlgebraicGeometry

/-- The pairing of `f : U ⟶ X` and `g : U ⟶ Y` as a pseudo-pullback cone over the
cospan of `baseProjection` morphisms. -/
noncomputable def pairOverBaseCone {S : Scheme.{u}} {X Y U : GroupoidsOver S} (f : U ⟶ X) (g : U ⟶ Y) :
    PseudoPullbackCone (baseProjection.{u + 1, u, u + 1} X)
      (baseProjection.{u + 1, u, u + 1} Y) where
  pt := U
  fst := f
  snd := g
  iso := baseProjection.naturality f ≪≫ (baseProjection.naturality g).symm

/-- The 1-morphism `U ⟶ X × Y` induced by a pair of 1-morphisms with common source,
where `X × Y` is the 2-fibre product of the two `baseProjection` morphisms. -/
noncomputable def pairOverBase {S : Scheme.{u}} {X Y U : GroupoidsOver S}
    (f : U ⟶ X) (g : U ⟶ Y) :
    U ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u}
        (baseProjection.{u + 1, u, u + 1} X)
        (baseProjection.{u + 1, u, u + 1} Y) :=
  PseudoPullbackCone.lift (pairOverBaseCone f g)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
      (baseProjection.{u + 1, u, u + 1} X)
      (baseProjection.{u + 1, u, u + 1} Y))

/-- The first projection of `pairOverBase f g` is isomorphic to `f`. -/
noncomputable def pairOverBase_fst {S : Scheme.{u}} {X Y U : GroupoidsOver S}
    (f : U ⟶ X) (g : U ⟶ Y) :
    pairOverBase f g ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u}
          (baseProjection.{u + 1, u, u + 1} X)
          (baseProjection.{u + 1, u, u + 1} Y) ≅
      f :=
  PseudoPullbackCone.lift.fstIso (pairOverBaseCone f g)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
      (baseProjection.{u + 1, u, u + 1} X)
      (baseProjection.{u + 1, u, u + 1} Y))

/-- The second projection of `pairOverBase f g` is isomorphic to `g`. -/
noncomputable def pairOverBase_snd {S : Scheme.{u}} {X Y U : GroupoidsOver S}
    (f : U ⟶ X) (g : U ⟶ Y) :
    pairOverBase f g ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u}
          (baseProjection.{u + 1, u, u + 1} X)
          (baseProjection.{u + 1, u, u + 1} Y) ≅
      g :=
  PseudoPullbackCone.lift.sndIso (pairOverBaseCone f g)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
      (baseProjection.{u + 1, u, u + 1} X)
      (baseProjection.{u + 1, u, u + 1} Y))

/-- `pairOverBase` is the universal lift of `pairOverBaseCone` into the 2-fibre
product of the two `baseProjection` morphisms. -/
theorem pairOverBase_eq {S : Scheme.{u}} {X Y U : GroupoidsOver S}
    (f : U ⟶ X) (g : U ⟶ Y) :
    pairOverBase f g =
      PseudoPullbackCone.lift (pairOverBaseCone f g)
        (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
          (baseProjection.{u + 1, u, u + 1} X)
          (baseProjection.{u + 1, u, u + 1} Y)) :=
  rfl

end AlgebraicGeometry
