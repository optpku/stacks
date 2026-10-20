module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.Finiteness
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic

/-!
# Unramified local complete-intersection morphisms

This file relates unramifiedness and formal unramifiedness for local complete-intersection
morphisms and records finite local freeness of their conormal sheaves.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyOfType

/-- A local complete-intersection morphism is unramified if and only if it is formally
unramified. -/
theorem unramified_iff_formallyUnramified
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    Unramified f ↔ FormallyUnramified f := sorry

end AlgebraicGeometry.LocallyOfType

namespace AlgebraicGeometry.Thickening.IsUniversalFirstOrder

/-- The conormal sheaf of a formally unramified local complete-intersection morphism is finite
locally free. -/
@[instance]
theorem conormalSheaf_isFiniteLocallyFree
    {Y : Scheme.{u}} (T : Thickening.Over Y)
    [FormallyUnramified T.left.hom]
    [LocallyOfType RingHom.IsLocalCompleteIntersection T.left.hom]
    [Thickening.IsUniversalFirstOrder T] :
    Scheme.Modules.IsFiniteLocallyFree (conormalSheaf T) := sorry

end AlgebraicGeometry.Thickening.IsUniversalFirstOrder
