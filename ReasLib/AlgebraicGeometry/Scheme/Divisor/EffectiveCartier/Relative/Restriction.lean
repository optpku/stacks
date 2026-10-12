/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative

/-!
# Restriction to a relative effective Cartier divisor

This file defines the restriction of an over-morphism to a divisor and records its
canonical flatness for a relative effective Cartier divisor.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The underlying composite defining the restriction of an over-morphism to a divisor
commutes with the structure morphisms. -/
theorem restrictedHom_comp {S : Scheme.{u}} {X Y : Over S}
    (D : X.left.IdealSheafData) (p : X ⟶ Y) :
    (D.subschemeι ≫ p.left) ≫ Y.hom = D.subschemeι ≫ X.hom := sorry

/-- The restriction to a divisor of a morphism of schemes over a fixed base. -/
def restrictedHom {S : Scheme.{u}} {X Y : Over S}
    (D : X.left.IdealSheafData) (p : X ⟶ Y) :
    Over.mk (D.subschemeι ≫ X.hom) ⟶ Y :=
  Over.homMk (D.subschemeι ≫ p.left) (restrictedHom_comp D p)

/-- The underlying scheme morphism of `D.restrictedHom p` is the expected composite. -/
theorem restrictedHom_left {S : Scheme.{u}} {X Y : Over S}
    (D : X.left.IdealSheafData) (p : X ⟶ Y) :
    (D.restrictedHom p).left = D.subschemeι ≫ p.left := sorry

/-- Restricting a morphism to a relative effective Cartier divisor gives a flat morphism. -/
instance restrictedHom_flat {S : Scheme.{u}} {X Y : Over S}
    (D : X.left.IdealSheafData) (p : X ⟶ Y)
    [IsRelativeEffectiveCartierDivisor p.left D] :
    Flat (D.restrictedHom p).left := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
