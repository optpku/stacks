/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Perfect.Composition

open CategoryTheory

universe u

/- The reusable perfect-ring-map composition API. -/
#check (RingHom.IsPerfectRingMap.stableUnderComposition :
  RingHom.StableUnderComposition (@RingHom.IsPerfectRingMap))

/- The reusable perfect-ring-map composition instance. -/
#check (RingHom.IsPerfectRingMap.comp :
  ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) [f.IsPerfectRingMap] [g.IsPerfectRingMap],
    (g.comp f).IsPerfectRingMap)

/- The reusable composition-stability instance for perfect scheme morphisms. -/
#check (AlgebraicGeometry.LocallyOfType.instIsPerfectRingMapStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsPerfectRingMap))

/- The reusable composition instance for perfect scheme morphisms. -/
#check (AlgebraicGeometry.LocallyOfType.isPerfectRingMap_comp :
  ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap f]
    [AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap g],
    AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap (f ≫ g))
