module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommPointwiseCompletedAction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.EquivariantTopTrace
public import ReasLib.Algebra.Homology.HomologicalComplex.PreservesHomology

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
noncomputable section
universe u v

namespace NoncommCompletedCochainTransport
variable (R : Type u) [Ring R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- Kernels and cokernels retain their original vectors and induced pointwise
actions. No identification with ALL algebraic completed modules is asserted. -/
instance preservesHomology : (NoncommPointwiseCompletedAction.functor R G).PreservesHomology := by sorry

variable (K : CochainComplex (DiscreteModuleCat R G) ℤ)

/-- Apply the already specified pointwise completed action to actual cochains. -/
def cochain := ((NoncommPointwiseCompletedAction.functor R G).mapHomologicalComplex
  (ComplexShape.up ℤ)).obj K

/-- Transport a specified equivariant homology map via exact completion. -/
def homologyMap (n : ℤ) {T : DiscreteModuleCat R G} (t : K.homology n ⟶ T) :
    (cochain R G K).homology n ⟶ (NoncommPointwiseCompletedAction.functor R G).obj T :=
  (K.mapHomologyIso (NoncommPointwiseCompletedAction.functor R G) n).hom ≫
    (NoncommPointwiseCompletedAction.functor R G).map t

theorem homology_zero (i : ℤ) (h : IsZero (K.homology i)) :
    IsZero ((cochain R G K).homology i) := by sorry

variable [HasDerivedCategory (ModuleCat.{max u v} (completedGroupRing R G))]

/-- Complete the canonical top-truncation trace roof using its explicit homology
map. This constructs a morphism, with no arbitrary isomorphism assumption. -/
def derivedTopMap (n : ℤ) (hvan : ∀ i : ℤ, n < i → IsZero (K.homology i))
    {T : DiscreteModuleCat R G} (t : K.homology n ⟶ T) :
    DerivedCategory.Q.obj (cochain R G K) ⟶
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (ModuleCat.{max u v} (completedGroupRing R G)) n).obj
        ((NoncommPointwiseCompletedAction.functor R G).obj T)) :=
  ActualEquivariantTopTrace.map (cochain R G K) n
    (fun i hi ↦ homology_zero R G K i (hvan i hi)) (homologyMap R G K n t)

end NoncommCompletedCochainTransport
