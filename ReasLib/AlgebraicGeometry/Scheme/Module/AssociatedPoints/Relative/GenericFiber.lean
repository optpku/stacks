module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative.GenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.GenericFiber

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- If the associated points of the generic fiber of a finite-type quasicoherent module are not
contained in an open subscheme, then this noncontainment persists over a nonempty open subscheme
of the irreducible base. -/
theorem exists_open_associatedPoints_fiber_not_subset
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (U : X.Opens)
    (hη : ¬ (((Scheme.Modules.pullback (f.fiberι (genericPoint Y))).obj ℱ).associatedPoints ⊆
      (f.fiberι (genericPoint Y)) ⁻¹' (U : Set X))) :
    ∃ V : Y.Opens, Nonempty V ∧
      ∀ y : Y, y ∈ V →
        ¬ (((Scheme.Modules.pullback (f.fiberι y)).obj ℱ).associatedPoints ⊆
          (f.fiberι y) ⁻¹' (U : Set X)) := sorry

/-- If the associated points of the generic fiber of a finite-type quasicoherent module are
contained in an open subscheme, then this containment persists over a nonempty open subscheme
of the irreducible base. -/
theorem exists_open_associatedPoints_fiber_subset
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (U : X.Opens)
    (hη : ((Scheme.Modules.pullback (f.fiberι (genericPoint Y))).obj ℱ).associatedPoints ⊆
      (f.fiberι (genericPoint Y)) ⁻¹' (U : Set X)) :
    ∃ V : Y.Opens, Nonempty V ∧
      ∀ y : Y, y ∈ V →
        ((Scheme.Modules.pullback (f.fiberι y)).obj ℱ).associatedPoints ⊆
          (f.fiberι y) ⁻¹' (U : Set X) := sorry

end AlgebraicGeometry.Scheme.Hom
