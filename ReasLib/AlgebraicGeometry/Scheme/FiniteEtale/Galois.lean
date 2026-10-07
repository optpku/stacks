module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Fiber
public import ReasLib.CategoryTheory.Galois.SetValued
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Data.Fintype.Shrink

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- The finite étale category over a connected scheme is a pre-Galois category. -/
instance preGaloisCategory {X : Scheme.{u}} [ConnectedSpace X] :
    PreGaloisCategory (FiniteEtale X) := sorry

variable {X : Scheme.{u}} [ConnectedSpace X] {K : Type u} [Field K] [IsAlgClosed K]

/-- Geometric fibers over a connected scheme preserve finite limits. -/
instance finiteFiber_preservesFiniteLimits (point : Spec (.of K) ⟶ X) :
    PreservesFiniteLimits (finiteFiber point) := sorry

/-- Geometric fibers over a connected scheme preserve finite colimits. -/
instance finiteFiber_preservesFiniteColimits (point : Spec (.of K) ⟶ X) :
    PreservesFiniteColimits (finiteFiber point) := sorry

/-- Geometric fibers over a connected scheme preserve epimorphisms. -/
instance finiteFiber_preservesEpimorphisms (point : Spec (.of K) ⟶ X) :
    Functor.PreservesEpimorphisms (finiteFiber point) := sorry

/-- Geometric fibers over a connected scheme reflect isomorphisms. -/
instance finiteFiber_reflectsIsomorphisms (point : Spec (.of K) ⟶ X) :
    (finiteFiber point).ReflectsIsomorphisms := sorry

/-- The finite geometric-fiber functor over a connected scheme is a fiber functor. -/
noncomputable instance finiteFiber_isFiberFunctor (point : Spec (.of K) ⟶ X) :
    FiberFunctor (finiteFiber point) where
  preservesTerminalObjects := inferInstance
  preservesPullbacks := inferInstance
  preservesFiniteCoproducts := inferInstance
  preservesEpis := inferInstance
  preservesQuotientsByFiniteGroups := fun group _ _ ↦
    @preservesColimitsOfShape_of_equiv _ _ _ _
      (SingleObj (Shrink.{0} group)) _ (SingleObj group) _
      (Shrink.mulEquiv.{0} (α := group)).toSingleObjEquiv (finiteFiber point)
      (@preservesColimitsOfShapeOfPreservesFiniteColimits _ _ _ _
        (finiteFiber point) inferInstance (SingleObj (Shrink.{0} group)) inferInstance
        (@SingleObj.finCategoryOfFintype (Shrink.{0} group)
          (Fintype.ofFinite _) inferInstance))
  reflectsIsos := inferInstance

/-- The finite étale category over a connected scheme is a Galois category. -/
instance galoisCategory {X : Scheme.{u}} [ConnectedSpace X] :
    GaloisCategory (FiniteEtale X) := sorry

/-- The specified set-valued geometric-fiber functor over a connected scheme is Galois. -/
theorem fiber_isGalois (point : Spec (.of K) ⟶ X) :
    Functor.IsGalois (fiber point) := sorry

end AlgebraicGeometry.Scheme.FiniteEtale
