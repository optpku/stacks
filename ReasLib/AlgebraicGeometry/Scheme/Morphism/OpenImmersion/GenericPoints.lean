module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.Sober

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry.IsOpenImmersion

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A separated morphism which is locally an open immersion on its source and is injective on
the generic points of its source is an open immersion. -/
theorem of_openCover_source_of_injOn_genericPoints
    [IsSeparated f]
    (hcov : ∃ 𝒰 : X.OpenCover, ∀ i, IsOpenImmersion (𝒰.f i ≫ f))
    (hgen : Set.InjOn f.base (genericPoints X)) :
    IsOpenImmersion f := sorry

end AlgebraicGeometry.IsOpenImmersion
