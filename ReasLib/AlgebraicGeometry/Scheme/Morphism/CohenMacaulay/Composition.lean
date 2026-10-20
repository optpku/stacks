module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Composition.Flat
public import ReasLib.RingTheory.Flat.Fiber.CohenMacaulay

/-!
# Composition of Cohen--Macaulay morphisms

This file records composition and cancellation properties for Cohen--Macaulay
morphisms of schemes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom.CohenMacaulayAt

/-- Cohen--Macaulayness at compatible points is preserved by composition when
the fibres of both morphisms and their composite are locally Noetherian. -/
theorem comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    [∀ y : Y, IsLocallyNoetherian (f.fiber y)]
    [∀ z : Z, IsLocallyNoetherian (g.fiber z)]
    [∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z)]
    (hf : f.CohenMacaulayAt x) (hg : g.CohenMacaulayAt (f x)) :
    (f ≫ g).CohenMacaulayAt x := sorry

end Scheme.Hom.CohenMacaulayAt

namespace CohenMacaulay

/-- The composite of Cohen--Macaulay morphisms is Cohen--Macaulay when the
fibres of both morphisms and their composite are locally Noetherian. -/
instance comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ y : Y, IsLocallyNoetherian (f.fiber y)]
    [∀ z : Z, IsLocallyNoetherian (g.fiber z)]
    [∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z)]
    [CohenMacaulay f] [CohenMacaulay g] : CohenMacaulay (f ≫ g) := sorry

end CohenMacaulay

namespace Scheme.Hom.CohenMacaulayAt

/-- If a composite is Cohen--Macaulay at a point and its first factor is flat
there, then both factors are Cohen--Macaulay at the corresponding points. -/
theorem of_comp_of_flatAt {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    [∀ y : Y, IsLocallyNoetherian (f.fiber y)]
    [∀ z : Z, IsLocallyNoetherian (g.fiber z)]
    [∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z)]
    (hfg : (f ≫ g).CohenMacaulayAt x) (hf : f.flatAt x) :
    f.CohenMacaulayAt x ∧ g.CohenMacaulayAt (f x) := sorry

end Scheme.Hom.CohenMacaulayAt

namespace CohenMacaulay

/-- If a composite is Cohen--Macaulay and its first factor is flat, then the
first factor is Cohen--Macaulay and the second is Cohen--Macaulay at every
point in the image of the first. -/
theorem of_comp_of_flat {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ y : Y, IsLocallyNoetherian (f.fiber y)]
    [∀ z : Z, IsLocallyNoetherian (g.fiber z)]
    [∀ z : Z, IsLocallyNoetherian ((f ≫ g).fiber z)]
    [CohenMacaulay (f ≫ g)] [Flat f] :
    CohenMacaulay f ∧
      ∀ y : Y, y ∈ Set.range f → g.CohenMacaulayAt y := sorry

end CohenMacaulay
end AlgebraicGeometry
