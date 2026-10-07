module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative.FlatPointClosure
import ReasLib.RingTheory.Module.Support.Flat

/-!
# Fiber-support dimension in flat families

This file gives a dimension bound for the supports of fibers of a finite-type
quasicoherent module that is flat over an irreducible base.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- For a finite-type quasicoherent module flat over an irreducible base, a bound on
the dimension of the support of the generic fiber bounds the support dimension of every fiber. -/
@[stacks 0H3X]
theorem topologicalKrullDim_moduleSupport_fiber_le {X S : Scheme.{u}} (f : X ⟶ S)
    (ℱ : X.Modules) [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    [IrreducibleSpace S] (hflat : flatOver ℱ f) {r : ℕ}
    (hη : topologicalKrullDim
      (moduleSupport ((Scheme.Modules.pullback (f.fiberι (genericPoint S))).obj ℱ)) ≤
        (r : WithBot ℕ∞)) (s : S) :
    topologicalKrullDim
      (moduleSupport ((Scheme.Modules.pullback (f.fiberι s)).obj ℱ)) ≤
        (r : WithBot ℕ∞) := sorry

end AlgebraicGeometry.Scheme.Modules
