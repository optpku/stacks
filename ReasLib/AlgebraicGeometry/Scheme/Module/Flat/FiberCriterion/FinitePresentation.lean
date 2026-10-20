module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Locus
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Cancellation
public import ReasLib.RingTheory.Flatness.LocalCriterion.ClosedFiber.FinitePresentation

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- At a point where a finitely presented module has nonzero stalk, flatness over the base
together with flatness on the fibre is equivalent to flatness of the intermediate scheme over
the base together with relative flatness of the module over the intermediate scheme. -/
theorem flatOverAt_and_fiber_iff_of_finitePresentation {S X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [LocallyOfFinitePresentation (f ≫ g)]
    [LocallyOfFiniteType g] (ℱ : X.Modules) [ℱ.IsFinitePresentation] (x : X)
    (h_stalk : ¬ IsZero (RingedSpace.stalkModuleCat ℱ x)) :
    (flatOverAt ℱ (f ≫ g) x ∧
      flatOverAt ((pullback ((f ≫ g).fiberι (g (f x)))).obj ℱ)
        (Scheme.Hom.compFiberToBaseFiber f g (g (f x))) ((f ≫ g).asFiber x)) ↔
      (Scheme.Hom.flatAt g (f x) ∧ flatOverAt ℱ f x) := sorry

/-- The locus in the support of a finitely presented module where the equivalent base-and-fibre
flatness conditions hold is relatively open in the support. -/
theorem isOpen_flatnessByFibersLocus {S X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [LocallyOfFinitePresentation (f ≫ g)]
    [LocallyOfFiniteType g] (ℱ : X.Modules) [ℱ.IsFinitePresentation] :
    IsOpen ((Subtype.val : moduleSupport ℱ → X) ⁻¹' {x : X |
      (flatOverAt ℱ (f ≫ g) x ∧
        flatOverAt ((pullback ((f ≫ g).fiberι (g (f x)))).obj ℱ)
          (Scheme.Hom.compFiberToBaseFiber f g (g (f x))) ((f ≫ g).asFiber x)) ∧
      (Scheme.Hom.flatAt g (f x) ∧ flatOverAt ℱ f x)}) := sorry

end AlgebraicGeometry.Scheme.Modules
