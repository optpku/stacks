/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ConstantGroup

/-!
# Points of the constant group algebraic space

Scheme-valued points of `G_B` over a morphism `t : ofOver T ⟶ B` are locally constant maps
`T → G`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization
open scoped AlgebraicGeometry CategoryTheory MonObj MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.ConstantGroup

/-- Morphisms over `B` from a scheme `T` to the constant group algebraic space `G_B` are
locally constant maps `T → G`. -/
def homMulEquiv {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GrpCat.{u})
    (T : Over S) (t : ofOver T ⟶ B) :
    (Over.mk t ⟶ (space B G).X) ≃* LocallyConstant T.left G where
  toFun f :=
    baseChangeHomMulEquiv S G T
      (Yoneda.fullyFaithful.homEquiv.symm
        (((Over.mapPullbackAdj (toBase B)).homEquiv (Over.mk t)
            (Over.mk (toBase (ofOver (baseChange S G).X)))).symm f).left)
  invFun a :=
    ((Over.mapPullbackAdj (toBase B)).homEquiv (Over.mk t)
        (Over.mk (toBase (ofOver (baseChange S G).X))))
      (Over.homMk (Yoneda.fullyFaithful.homEquiv ((baseChangeHomMulEquiv S G T).symm a)) sorry)
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry

/-- The forward map of `homMulEquiv` is the composite of the pullback adjunction, Yoneda, and
`baseChangeHomMulEquiv`. -/
theorem homMulEquiv_apply {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GrpCat.{u})
    (T : Over S) (t : ofOver T ⟶ B) (f : Over.mk t ⟶ (space B G).X) :
    homMulEquiv G T t f =
      baseChangeHomMulEquiv S G T
        (Yoneda.fullyFaithful.homEquiv.symm
          (((Over.mapPullbackAdj (toBase B)).homEquiv (Over.mk t)
              (Over.mk (toBase (ofOver (baseChange S G).X)))).symm f).left) :=
  sorry

/-- Precomposition of points over `B` corresponds to precomposition of locally constant maps. -/
theorem homMulEquiv_naturality {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GrpCat.{u})
    (T T' : Over S) (baseMap : ofOver T ⟶ B) (baseMap' : ofOver T' ⟶ B)
    (testMap : T' ⟶ T) (h_over : SchemeRealization.ofOverMap testMap ≫ baseMap = baseMap')
    (point : Over.mk baseMap ⟶ (space B G).X) :
    homMulEquiv G T' baseMap'
        (Over.homMk (V := Over.mk baseMap) (SchemeRealization.ofOverMap testMap) h_over ≫ point) =
      pointsMap G testMap (homMulEquiv G T baseMap point) := sorry

/-- The Type `u` fibre of morphisms over `B` from a scheme `T` into `space B G`. -/
def pointsFibre {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GrpCat.{u})
    (T : Over S) (t : ofOver T ⟶ B) : Type u :=
  { s : (space B G).X.left.functorOfPoints.obj (op T) //
    (space B G).X.hom.app (op T) s = yonedaEquiv t }

/-- The comparison from the fibre of `T`-points over `t` to morphisms over `B`. -/
def pointsFibreHomEquiv {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GrpCat.{u})
    (T : Over S) (t : ofOver T ⟶ B) :
    pointsFibre G T t ≃ (Over.mk t ⟶ (space B G).X) where
  toFun s := Over.homMk (yonedaEquiv.symm s.1) sorry
  invFun f := ⟨yonedaEquiv f.left, sorry⟩
  left_inv := sorry
  right_inv := sorry

/-- Scheme-valued points of `G_B` over `t` in Type `u` are locally constant maps `T → G`. -/
def pointsFibreEquiv {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GrpCat.{u})
    (T : Over S) (t : ofOver T ⟶ B) :
    pointsFibre G T t ≃ LocallyConstant T.left G :=
  (pointsFibreHomEquiv G T t).trans (homMulEquiv G T t).toEquiv

/-- The forward map of `pointsFibreEquiv` is the composite of `pointsFibreHomEquiv` with
`homMulEquiv`. -/
theorem pointsFibreEquiv_apply {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GrpCat.{u})
    (T : Over S) (t : ofOver T ⟶ B) (s : pointsFibre G T t) :
    pointsFibreEquiv G T t s = homMulEquiv G T t (pointsFibreHomEquiv G T t s) :=
  sorry

end AlgebraicGeometry.ConstantGroup
