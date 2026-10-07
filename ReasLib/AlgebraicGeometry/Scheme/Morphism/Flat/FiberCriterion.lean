module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.FiberCriterion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.FiberCriterion.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Descent

/-!
# Flatness criteria from fibers

This file records flatness criteria for scheme morphisms from their behavior on fibers,
under locally Noetherian or finite-presentation hypotheses.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.FlatnessByFibers

/-- A morphism between locally Noetherian schemes is flat if its composite to the base and
all its induced morphisms on fibers are flat. -/
theorem of_isLocallyNoetherian {S X Y : Scheme.{u}}
    [IsLocallyNoetherian S] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (g : Y ⟶ S) [Flat (f ≫ g)]
    [∀ s : S, Flat (compFiberToBaseFiber f g s)] :
    Flat f := sorry

/-- If the morphism in the fiberwise flatness criterion is surjective, then its locally
Noetherian target is flat over the base. -/
theorem base_of_surjective_of_isLocallyNoetherian {S X Y : Scheme.{u}}
    [IsLocallyNoetherian S] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (g : Y ⟶ S) [Flat (f ≫ g)]
    [∀ s : S, Flat (compFiberToBaseFiber f g s)] [Surjective f] :
    Flat g := sorry

/-- A morphism of schemes is flat if its composite to the base is flat and locally of finite
presentation, every induced morphism on fibers is flat, and its target is locally of finite type
over the base. -/
theorem of_finitePresentation {S X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [LocallyOfFinitePresentation (f ≫ g)] [Flat (f ≫ g)]
    [∀ s : S, Flat (compFiberToBaseFiber f g s)] [LocallyOfFiniteType g] :
    Flat f := sorry

/-- If the morphism in the finite-presentation fiberwise flatness criterion is surjective, then
its target is flat over the base. -/
theorem base_of_surjective_of_finitePresentation {S X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [LocallyOfFinitePresentation (f ≫ g)] [Flat (f ≫ g)]
    [∀ s : S, Flat (compFiberToBaseFiber f g s)] [LocallyOfFiniteType g]
    [Surjective f] :
    Flat g := sorry

end AlgebraicGeometry.Scheme.Hom.FlatnessByFibers
