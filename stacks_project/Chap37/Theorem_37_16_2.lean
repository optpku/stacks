module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.FiberCriterion.FinitePresentation

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Theorem 37.16.2: at a point where the stalk of `ℱ` is nonzero, flatness of `ℱ` over
the base together with flatness on the fibre is equivalent to flatness of the intermediate
scheme over the base together with flatness of `ℱ` over the intermediate scheme. -/
@[stacks 039C] #check
  (AlgebraicGeometry.Scheme.Modules.flatOverAt_and_fiber_iff_of_finitePresentation :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
      [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g]
      (ℱ : X.Modules) [ℱ.IsFinitePresentation] (x : X)
      (h_stalk : ¬ IsZero (RingedSpace.stalkModuleCat ℱ x)),
      (flatOverAt ℱ (f ≫ g) x ∧
        flatOverAt ((pullback ((f ≫ g).fiberι (g (f x)))).obj ℱ)
          (Scheme.Hom.compFiberToBaseFiber f g (g (f x))) ((f ≫ g).asFiber x)) ↔
        (Scheme.Hom.flatAt g (f x) ∧ flatOverAt ℱ f x))

/- The openness clause identifies the common flatness-by-fibres locus as an open subset of
`moduleSupport ℱ`. -/
#check
  (AlgebraicGeometry.Scheme.Modules.isOpen_flatnessByFibersLocus :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
      [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g]
      (ℱ : X.Modules) [ℱ.IsFinitePresentation],
      IsOpen ((Subtype.val : moduleSupport ℱ → X) ⁻¹' {x : X |
        (flatOverAt ℱ (f ≫ g) x ∧
          flatOverAt ((pullback ((f ≫ g).fiberι (g (f x)))).obj ℱ)
            (Scheme.Hom.compFiberToBaseFiber f g (g (f x))) ((f ≫ g).asFiber x)) ∧
        (Scheme.Hom.flatAt g (f x) ∧ flatOverAt ℱ f x)}))

end AlgebraicGeometry.Scheme.Modules
