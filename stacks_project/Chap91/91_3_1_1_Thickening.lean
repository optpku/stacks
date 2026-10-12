/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening

/-!
# Thickenings of ringed spaces

A morphism of ringed spaces is a thickening when the underlying map is a homeomorphism, the
structure-sheaf map is locally surjective, and the kernel ideal sheaf is locally nilpotent.
-/

open CategoryTheory

universe u

#check (AlgebraicGeometry.RingedSpace.isThickening_iff :
  {X X' : AlgebraicGeometry.RingedSpace.{u}} → (i : X ⟶ X') →
    AlgebraicGeometry.RingedSpace.IsThickening i ↔
      IsIso i.hom.base ∧ TopCat.Presheaf.IsLocallySurjective i.hom.c ∧
        (AlgebraicGeometry.RingedSpace.Hom.kernelIdealSubobject i).IsLocallyNilpotent)
