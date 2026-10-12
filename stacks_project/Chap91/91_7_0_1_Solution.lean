/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution

/-!
# Compatibility checks for first-order deformation solutions
-/

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

#check (AlgebraicGeometry.RingedSpace.Thickening.kernelMapOf :
  {S S' X : AlgebraicGeometry.RingedSpace.{u}} →
    (t : S ⟶ S') → [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening t] →
    (f : X ⟶ S) → {X' : AlgebraicGeometry.RingedSpace.{u}} →
    (i : X ⟶ X') → AlgebraicGeometry.RingedSpace.IsFirstOrderThickening i →
    (f' : X' ⟶ S') → i ≫ f' = f ≫ t →
    (AlgebraicGeometry.RingedSpace.Hom.idealModule t ⟶
      (f _*).obj (AlgebraicGeometry.RingedSpace.Hom.idealModule i)))
#check (AlgebraicGeometry.RingedSpace.Thickening.cPull :
  {S S' X : AlgebraicGeometry.RingedSpace.{u}} →
    (t : S ⟶ S') →
    (f : X ⟶ S) → {G : X.Modules} →
    (AlgebraicGeometry.RingedSpace.Hom.idealModule t ⟶ (f _*).obj G) →
    ((f^*).obj (AlgebraicGeometry.RingedSpace.Hom.idealModule t) ⟶ G))
#check (AlgebraicGeometry.RingedSpace.Thickening.Solution :
  {S S' X : AlgebraicGeometry.RingedSpace.{u}} →
    (t : S ⟶ S') → [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening t] →
    (f : X ⟶ S) → (G : X.Modules) →
    (AlgebraicGeometry.RingedSpace.Hom.idealModule t ⟶ (f _*).obj G) → Type (u + 1))
