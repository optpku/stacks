/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommReversedCharacterComplex
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommResidualDualComplex

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
noncomputable section
universe u

namespace NoncommCharacterDegreeComparison
variable (R G : Type u) [Ring R] [Finite R]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable (J : CochainComplex (DiscreteModuleCat R G) ℕ)

def chain : ChainComplex (NoncommCompactRepresentation.Cat Rᵐᵒᵖ G) ℕ where
  X i := NoncommRepresentationDuality.dual R G (J.X i)
  d i j := NoncommRepresentationDuality.dualMap R G (J.d j i)
  shape := by sorry
  d_comp_d' := by sorry

def extended := (((NoncommCompletedAction.functor Rᵐᵒᵖ G).mapHomologicalComplex
  (ComplexShape.down ℕ)).obj (chain R G J)).extend CompactRepresentation.curveDegreeEmbedding

abbrev reversed := NoncommReversedCharacterComplex.completed R G (J.extend ComplexShape.embeddingUpNat)

/-- Above degree 2 the argument is a genuinely zero extension in negative
degree. Only these out-of-support components are zero. -/
theorem reversed_zero (i : ℤ) (hi : 2 < i) : IsZero ((reversed R G J).X i) := by sorry
theorem extended_zero (i : ℤ) (hi : 2 < i) : IsZero ((extended R G J).X i) := by sorry

/-- Within support, use the actual two extension identifications and character
precomposition. Outside support use the canonical comparison of proved zero objects. -/
def componentIso (i : ℤ) : (reversed R G J).X i ≅ (extended R G J).X i :=
  if hi : i ≤ 2 then
    (NoncommCompletedAction.functor Rᵐᵒᵖ G).mapIso
      ((NoncommRepresentationDuality.dualFunctor R G).mapIso
        (J.extendXIso ComplexShape.embeddingUpNat (i := (2 - i).toNat) (i' := 2 - i)
          (by change ((2 - i).toNat : ℤ) = 2 - i; omega)).symm.op) ≪≫
    ((((NoncommCompletedAction.functor Rᵐᵒᵖ G).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (chain R G J)).extendXIso CompactRepresentation.curveDegreeEmbedding
        (i := (2 - i).toNat) (i' := i) (by change 2 - ((2 - i).toNat : ℤ) = i; omega)).symm
  else (reversed_zero R G J i (by omega)).iso (extended_zero R G J i (by omega))

/-- The unsigned reverse/extension comparison on actual character maps. -/
def iso : reversed R G J ≅ extended R G J :=
  HomologicalComplex.Hom.isoOfComponents (componentIso R G J) (by sorry)

/-- Apply the SAME phase convention on both sides; degree 2 remains normalized. -/
def signedIso : ActualCurveHomSign.signed (reversed R G J) ≅ ActualCurveHomSign.signed (extended R G J) :=
  (ActualCurveHomSign.iso (reversed R G J)).symm ≪≫ iso R G J ≪≫
    ActualCurveHomSign.iso (extended R G J)

end NoncommCharacterDegreeComparison
