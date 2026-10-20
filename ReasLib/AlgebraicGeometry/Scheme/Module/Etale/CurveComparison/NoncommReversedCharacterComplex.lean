module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommCompletedAction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommRepresentationDuality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CurveHomSign
public import ReasLib.Algebra.Homology.HomologicalComplex.PreservesHomology

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
noncomputable section
universe u

namespace NoncommReversedCharacterComplex
variable (R G : Type u) [Ring R] [Finite R]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable (K : CochainComplex (DiscreteModuleCat R G) ℤ)

/-- Actual compact characters in degree 2-i, with unsigned precomposition. -/
def reverse : CochainComplex (NoncommCompactRepresentation.Cat Rᵐᵒᵖ G) ℤ where
  X i := NoncommRepresentationDuality.dual R G (K.X (2 - i))
  d i j := NoncommRepresentationDuality.dualMap R G (K.d (2 - j) (2 - i))
  shape := by sorry
  d_comp_d' := by sorry

variable {K} {L : CochainComplex (DiscreteModuleCat R G) ℤ}

/-- Reverse an actual cochain map by character precomposition. -/
def reverseMap (f : K ⟶ L) : reverse R G L ⟶ reverse R G K where
  f i := NoncommRepresentationDuality.dualMap R G (f.f (2 - i))
  comm' := by sorry

/-- Exact continuous-character duality, not algebraic biduality, preserves
quasi-isomorphisms under this reversal. -/
theorem reverseMap_quasiIso (f : K ⟶ L) [QuasiIso f] : QuasiIso (reverseMap R G f) := by sorry

instance completion_preservesHomology : (NoncommCompletedAction.functor Rᵐᵒᵖ G).PreservesHomology := by sorry

variable (K)
def completed := ((NoncommCompletedAction.functor Rᵐᵒᵖ G).mapHomologicalComplex
  (ComplexShape.up ℤ)).obj (reverse R G K)

def signed := ActualCurveHomSign.signed (completed R G K)

variable {K}

/-- Complete the same precomposition maps and apply the fixed involutive phases. -/
def map (f : K ⟶ L) : signed R G L ⟶ signed R G K :=
  (ActualCurveHomSign.iso (completed R G L)).inv ≫
    ((NoncommCompletedAction.functor Rᵐᵒᵖ G).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (reverseMap R G f) ≫
    (ActualCurveHomSign.iso (completed R G K)).hom

theorem map_quasiIso (f : K ⟶ L) [QuasiIso f] : QuasiIso (map R G f) := by sorry

variable [HasDerivedCategory (ModuleCat.{u} (completedGroupRing Rᵐᵒᵖ G))]

/-- A specified cochain quasi-isomorphism gives its specified signed-character
derived isomorphism. This does not choose a map between unrelated models. -/
def isoOfQuasiIso (f : K ⟶ L) [QuasiIso f] :
    DerivedCategory.Q.obj (signed R G L) ≅ DerivedCategory.Q.obj (signed R G K) :=
  -- Local instance justification (proof-local temporary data): exact compact duality for this particular f.
  letI := map_quasiIso R G f
  asIso (DerivedCategory.Q.map (map R G f))

end NoncommReversedCharacterComplex
