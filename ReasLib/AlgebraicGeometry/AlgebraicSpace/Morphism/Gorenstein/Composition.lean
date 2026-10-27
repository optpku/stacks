/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Gorenstein.Global
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.LocallyNoetherian

/-!
# Composition of Gorenstein morphisms of algebraic spaces

Gorensteinness is preserved by composition when the fibres of both factors and
their composite are locally Noetherian. Under flatness of the first factor,
Gorensteinness of the composite also implies Gorensteinness of both factors at
compatible points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace GorensteinAt

/-- For morphisms of algebraic spaces whose fibres and composite fibres are locally
Noetherian, Gorensteinness at compatible points is preserved by composition. -/
@[stacks 0E16]
theorem comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyNoetherianFibers f] [LocallyNoetherianFibers g]
    [LocallyNoetherianFibers (f ≫ g)] (x : Points X)
    (hf : GorensteinAt f x) (hg : GorensteinAt g (Points.map f x)) :
    GorensteinAt (f ≫ g) x :=
  sorry

end GorensteinAt

namespace Gorenstein

/-- The composite of Gorenstein morphisms of algebraic spaces is Gorenstein when
the fibres of both factors and their composite are locally Noetherian. -/
@[stacks 0E16]
instance comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyNoetherianFibers f] [LocallyNoetherianFibers g]
    [LocallyNoetherianFibers (f ≫ g)] [Gorenstein f] [Gorenstein g] :
    Gorenstein (f ≫ g) :=
  sorry

end Gorenstein

namespace GorensteinAt

/-- If a composite of morphisms of algebraic spaces is Gorenstein at a point and
the first factor is flat there, both factors are Gorenstein at the corresponding
points, provided all three morphisms have locally Noetherian fibres. -/
@[stacks 0E16]
theorem of_comp_of_flatAt {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyNoetherianFibers f] [LocallyNoetherianFibers g]
    [LocallyNoetherianFibers (f ≫ g)] (x : Points X)
    (hfg : GorensteinAt (f ≫ g) x) (hf : FlatAt f x) :
    GorensteinAt f x ∧ GorensteinAt g (Points.map f x) :=
  sorry

end GorensteinAt

namespace Gorenstein

/-- If a composite of morphisms of algebraic spaces is Gorenstein and the first
factor is flat, the first factor is Gorenstein and the second is Gorenstein on
the image of the first, provided all three morphisms have locally Noetherian fibres. -/
@[stacks 0E16]
theorem of_comp_of_flat {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyNoetherianFibers f] [LocallyNoetherianFibers g]
    [LocallyNoetherianFibers (f ≫ g)] [Gorenstein (f ≫ g)] [Flat f] :
    Gorenstein f ∧
      ∀ y : Points Y, y ∈ Set.range (Points.map f) → GorensteinAt g y :=
  sorry

end Gorenstein

end AlgebraicGeometry.AlgebraicSpace
