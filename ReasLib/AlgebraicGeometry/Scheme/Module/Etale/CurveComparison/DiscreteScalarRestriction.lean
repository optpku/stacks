module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommPointwiseCompletedAction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommCompletedTransport
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ModuleRestrictionIso

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
noncomputable section
universe u v

namespace DiscreteScalarRestriction
variable {S T : Type u} [Ring S] [Ring T] (h : S →+* T)
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Change coefficients on the original vectors and group action. Open
stabilizers are unchanged, not replaced by a whole-action kernel. -/
def functor : DiscreteModuleCat T G ⥤ DiscreteModuleCat S G where
  obj M := ⟨((ModuleCat.restrictScalars.{max u v} h).mapAction G).obj M.obj, by sorry⟩
  map f := ObjectProperty.homMk (((ModuleCat.restrictScalars.{max u v} h).mapAction G).map f.hom)
  map_id := by intros; rfl
  map_comp := by intros; rfl

instance functor_additive : (functor h G).Additive := by sorry
instance functor_preservesFiniteLimits : PreservesFiniteLimits (functor h G) := by sorry
instance functor_preservesFiniteColimits : PreservesFiniteColimits (functor h G) := by sorry

variable [CompactSpace G]

/-- Actual coefficient restriction commutes with pointwise completed action:
every scalar is evaluated at a finite normal subgroup fixing the same vector. -/
def completionIso (M : DiscreteModuleCat T G) :
    (NoncommPointwiseCompletedAction.functor S G).obj ((functor h G).obj M) ≅
    (ModuleCat.restrictScalars (NoncommCompletedTransport.coefficientHom S (G := G) h)).obj
      ((NoncommPointwiseCompletedAction.functor T G).obj M) :=
  (ActualModuleRestriction.restrictionIso (NoncommCompletedTransport.coefficientHom S (G := G) h)
    ((NoncommPointwiseCompletedAction.functor T G).obj M)
    ((NoncommPointwiseCompletedAction.functor S G).obj ((functor h G).obj M))
    (AddEquiv.refl _) (by sorry)).symm

/-- The comparison is identity on vectors and natural in every actual coefficient map. -/
def completionNatIso : functor h G ⋙ NoncommPointwiseCompletedAction.functor S G ≅
    NoncommPointwiseCompletedAction.functor T G ⋙
      ModuleCat.restrictScalars (NoncommCompletedTransport.coefficientHom S (G := G) h) :=
  NatIso.ofComponents (completionIso h G) (by sorry)

end DiscreteScalarRestriction
