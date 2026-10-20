module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FirstOrder

/-!
# First-order thickenings of algebraic spaces

The square-zero closed-immersion property and its characterization.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening :
  ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S}, (X ⟶ X') → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isFirstOrderThickening_iff :
  ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X'),
    IsFirstOrderThickening i ↔
      IsClosedImmersion i ∧
        Modules.idealAction (Hom.idealSheafSubobject i) (Hom.idealSheaf i) = 0)
