module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.AssociatedPoints
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Theorem 38.26.1: a finite-type quasicoherent module is flat over the base at `x`
if and only if it is flat at every associated point of the fiber over `f x` that
specializes to `x`. -/
@[stacks 05UA] #check
  (AlgebraicGeometry.Scheme.Modules.flatOverAt_iff_associatedPoints_specializingTo :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
        (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (x : X),
      flatOverAt ℱ f x ↔
        ∀ x' : f.fiber (f x),
          x' ∈ ((Scheme.Modules.pullback (f.fiberι (f x))).obj ℱ).associatedPoints →
            f.fiberι (f x) x' ⤳ x → flatOverAt ℱ f (f.fiberι (f x) x'))

end AlgebraicGeometry.Scheme.Modules
