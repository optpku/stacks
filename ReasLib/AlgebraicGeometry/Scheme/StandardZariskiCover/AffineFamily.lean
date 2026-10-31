/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily.AffineOver
public import ReasLib.AlgebraicGeometry.Scheme.StandardZariskiCover

/-!
# Affine-slice realizations of standard Zariski covers

This leaf realizes an arbitrarily indexed finite standard Zariski cover as a
family in an affine slice. It preserves the cover's index type rather than
choosing an enumeration by `Fin n`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

namespace StandardZariskiCover

variable {T : Scheme.{u}}

/-- The `i`-th member of a standard Zariski cover of the source of an affine
`S`-scheme, regarded as an affine object over `S`. -/
@[stacks 020T "affine-slice object of a standard Zariski cover"]
def affineOverObj {S : Scheme.{u}} (U : S.AffineOver)
    (𝒰 : U.obj.left.StandardZariskiCover.{u, v}) (i : 𝒰.index) : S.AffineOver :=
  AffineOver.mk _ (𝒰.isAffine_obj i) (𝒰.f i ≫ U.obj.hom)

/-- The compatibility equation used to regard a distinguished-open immersion as a morphism in
the affine slice. -/
@[stacks 020T "standard Zariski cover slice factorization"]
theorem affineOverMap_fac {S : Scheme.{u}} (U : S.AffineOver)
    (𝒰 : U.obj.left.StandardZariskiCover.{u, v}) (i : 𝒰.index) :
    𝒰.f i ≫ U.obj.hom = (affineOverObj U 𝒰 i).obj.hom :=
  rfl

/-- The arrow from a standard distinguished-open member to its affine-slice
target. -/
@[stacks 020T "affine-slice map of a standard Zariski cover"]
def affineOverMap {S : Scheme.{u}} (U : S.AffineOver)
    (𝒰 : U.obj.left.StandardZariskiCover.{u, v}) (i : 𝒰.index) :
    affineOverObj U 𝒰 i ⟶ U :=
  AffineOver.homMk (𝒰.f i) (affineOverMap_fac U 𝒰 i)

/-- The presieve on an affine `S`-scheme represented by a standard Zariski
cover of its source scheme. -/
@[stacks 020T "affine-slice presieve of a standard Zariski cover"]
def affineOverPresieve {S : Scheme.{u}} (U : S.AffineOver)
    (𝒰 : U.obj.left.StandardZariskiCover.{u, v}) : Presieve U :=
  Presieve.ofArrows (affineOverObj U 𝒰) (affineOverMap U 𝒰)

/-- The object of `Over S` underlying a standard-cover chart is the composite
of the distinguished-open immersion with the structure map of the target. -/
@[simp, stacks 020T "standard Zariski cover slice object readout"]
theorem affineOverObj_obj {S : Scheme.{u}} (U : S.AffineOver)
    (𝒰 : U.obj.left.StandardZariskiCover.{u, v}) (i : 𝒰.index) :
    (affineOverObj U 𝒰 i).obj = Over.mk (𝒰.f i ≫ U.obj.hom) :=
  rfl

/-- Applying the affine-slice inclusion to a standard-cover chart arrow
recovers its underlying arrow in `Over S`. -/
@[simp, stacks 020T "standard Zariski cover slice map readout"]
theorem forget_affineOverMap {S : Scheme.{u}} (U : S.AffineOver)
    (𝒰 : U.obj.left.StandardZariskiCover.{u, v}) (i : 𝒰.index) :
    (AffineOver.forget S).map (affineOverMap U 𝒰 i) =
      Over.homMk (𝒰.f i) (affineOverMap_fac U 𝒰 i) :=
  rfl

end StandardZariskiCover

end AlgebraicGeometry.Scheme
