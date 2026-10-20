module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.FiniteGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Relative

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

/-- For a locally finite type morphism, the relative weak assassin of a quasicoherent module
equals its relative assassin. -/
theorem relativeWeakAss_eq_relativeAssassin_of_locallyOfFiniteType
    (f : X ⟶ S) [LocallyOfFiniteType f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    relativeWeakAss f ℱ = relativeAssassin f ℱ := sorry

/-- For a locally finite type morphism, relative weakly associated membership is equivalent to
relative associated membership. -/
@[simp]
theorem mem_relativeWeakAss_iff_mem_relativeAssassin_of_locallyOfFiniteType
    (f : X ⟶ S) [LocallyOfFiniteType f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] (x : X) :
    x ∈ relativeWeakAss f ℱ ↔ x ∈ relativeAssassin f ℱ := sorry

end AlgebraicGeometry.Scheme.Modules
