module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.relativeAssassin

/-- A relatively associated point of a finite-type quasicoherent module admits a nonempty open
subscheme of its reduced closure whose fiberwise generic points remain relatively associated. -/
theorem exists_open_pointClosure_fiber_genericPoints
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    {ξ : X} (hξ : ξ ∈ relativeAssassin f ℱ) :
    ∃ V : (PointClosure.scheme ξ).Opens, Nonempty V ∧
      ∀ s : S, s ∈ Set.range (V.ι ≫ PointClosure.ι ξ ≫ f).base →
        Set.MapsTo
          ((V.ι ≫ PointClosure.ι ξ ≫ f).fiberι s ≫ V.ι ≫ PointClosure.ι ξ).base
          (genericPoints ((V.ι ≫ PointClosure.ι ξ ≫ f).fiber s))
          (relativeAssassin f ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules.relativeAssassin
