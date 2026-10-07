module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.FiberCriterion

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Theorem 37.16.1: for a coherent quasi-coherent module with nonzero stalk on locally
Noetherian schemes, flatness over the base together with flatness on the fibre is equivalent to
flatness of the intermediate scheme over the base together with relative flatness over the
intermediate scheme. -/
@[stacks 039B] #check
  (AlgebraicGeometry.Scheme.Modules.flatOverAt_and_fiber_iff :
    ∀ {S X Y : Scheme.{u}}
      [IsLocallyNoetherian S] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
      (f : X ⟶ Y) (g : Y ⟶ S) (ℱ : X.Modules)
      [ℱ.IsQuasicoherent] [ℱ.IsCoherent] (x : X)
      (h_stalk : ¬ IsZero (RingedSpace.stalkModuleCat ℱ x)),
      (flatOverAt ℱ (f ≫ g) x ∧
        flatOverAt ((pullback ((f ≫ g).fiberι (g (f x)))).obj ℱ)
          (Scheme.Hom.compFiberToBaseFiber f g (g (f x))) ((f ≫ g).asFiber x)) ↔
        (Scheme.Hom.flatAt g (f x) ∧ flatOverAt ℱ f x))

end AlgebraicGeometry.Scheme.Modules
