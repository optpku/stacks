/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Composition.Flat
public import ReasLib.RingTheory.Gorenstein.FlatLocal

/-!
# Composition and cancellation of Gorenstein scheme morphisms

This file records composition and flat-cancellation properties for Gorenstein
morphisms of schemes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom.gorensteinAt

/-- Gorensteinness at compatible points is preserved by composition when the
fibres of both morphisms and their composite are locally Noetherian. -/
theorem comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    [∀ y : Y, IsLocallyNoetherian (f.fiber y)]
    [∀ z : Z, IsLocallyNoetherian (g.fiber z)]
    [∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z)]
    (hf : f.gorensteinAt x) (hg : g.gorensteinAt (f x)) :
    (f ≫ g).gorensteinAt x := sorry

end Scheme.Hom.gorensteinAt

namespace Gorenstein

/-- The composite of Gorenstein morphisms is Gorenstein when the fibres of both
morphisms and their composite are locally Noetherian. -/
instance comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ y : Y, IsLocallyNoetherian (f.fiber y)]
    [∀ z : Z, IsLocallyNoetherian (g.fiber z)]
    [∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z)]
    [Gorenstein f] [Gorenstein g] : Gorenstein (f ≫ g) := sorry

end Gorenstein

namespace Scheme.Hom.gorensteinAt

/-- If a composite is Gorenstein at a point and its first factor is flat there,
then both factors are Gorenstein at the corresponding points. -/
theorem of_comp_of_flatAt {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    [∀ y : Y, IsLocallyNoetherian (f.fiber y)]
    [∀ z : Z, IsLocallyNoetherian (g.fiber z)]
    [∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z)]
    (hfg : (f ≫ g).gorensteinAt x) (hf : f.flatAt x) :
    f.gorensteinAt x ∧ g.gorensteinAt (f x) := sorry

end Scheme.Hom.gorensteinAt

namespace Gorenstein

/-- If a composite is Gorenstein and its first factor is flat, then the first
factor is Gorenstein and the second is Gorenstein at every point in the image
of the first. -/
theorem of_comp_of_flat {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ y : Y, IsLocallyNoetherian (f.fiber y)]
    [∀ z : Z, IsLocallyNoetherian (g.fiber z)]
    [∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z)]
    [Gorenstein (f ≫ g)] [Flat f] :
    Gorenstein f ∧
      ∀ y : Y, y ∈ Set.range f → g.gorensteinAt y := sorry

end Gorenstein
end AlgebraicGeometry
