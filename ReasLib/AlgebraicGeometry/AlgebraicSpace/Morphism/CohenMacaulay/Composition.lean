/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.CohenMacaulay

/-!
# Composition of Cohen--Macaulay morphisms of algebraic spaces

Cohen--Macaulayness of morphisms of algebraic spaces is stable under
composition, pointwise and globally, when the fibres of both morphisms and
of the composite are locally Noetherian. Under a flatness hypothesis on the
first factor it also cancels, pointwise and on the image of that factor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace CohenMacaulayAt

/-- For morphisms of algebraic spaces whose fibres and composite fibres are locally
Noetherian, Cohen--Macaulayness at compatible points is preserved by composition. -/
@[stacks 0E0X]
theorem comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyNoetherianFibers f] [LocallyNoetherianFibers g]
    [LocallyNoetherianFibers (f ≫ g)] (x : Points X)
    (hf : CohenMacaulayAt f x) (hg : CohenMacaulayAt g (Points.map f x)) :
    CohenMacaulayAt (f ≫ g) x :=
  sorry

end CohenMacaulayAt

namespace CohenMacaulay

/-- The composite of Cohen--Macaulay morphisms of algebraic spaces is
Cohen--Macaulay when the fibres of both factors and their composite are locally
Noetherian. -/
@[stacks 0E0X]
instance comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyNoetherianFibers f] [LocallyNoetherianFibers g]
    [LocallyNoetherianFibers (f ≫ g)] [CohenMacaulay f] [CohenMacaulay g] :
    CohenMacaulay (f ≫ g) :=
  sorry

end CohenMacaulay

namespace CohenMacaulayAt

/-- If a composite of morphisms of algebraic spaces is Cohen--Macaulay at a point
and the first factor is flat there, both factors are Cohen--Macaulay at the
corresponding points, provided all three morphisms have locally Noetherian fibres. -/
@[stacks 0E0X]
theorem of_comp_of_flatAt {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyNoetherianFibers f] [LocallyNoetherianFibers g]
    [LocallyNoetherianFibers (f ≫ g)] (x : Points X)
    (hfg : CohenMacaulayAt (f ≫ g) x) (hf : FlatAt f x) :
    CohenMacaulayAt f x ∧ CohenMacaulayAt g (Points.map f x) :=
  sorry

end CohenMacaulayAt

namespace CohenMacaulay

/-- If a composite of morphisms of algebraic spaces is Cohen--Macaulay and the
first factor is flat, the first factor is Cohen--Macaulay and the second is
Cohen--Macaulay on the image of the first factor, provided all three morphisms
have locally Noetherian fibres. -/
@[stacks 0E0X]
theorem of_comp_of_flat {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyNoetherianFibers f] [LocallyNoetherianFibers g]
    [LocallyNoetherianFibers (f ≫ g)] [CohenMacaulay (f ≫ g)] [Flat f] :
    CohenMacaulay f ∧
      ∀ y : Points Y, y ∈ Set.range (Points.map f) → CohenMacaulayAt g y :=
  sorry

end CohenMacaulay

end AlgebraicGeometry.AlgebraicSpace
