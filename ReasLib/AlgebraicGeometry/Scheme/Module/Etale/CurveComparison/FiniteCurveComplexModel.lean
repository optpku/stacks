module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteThreeTermModel
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
noncomputable section
universe u v

namespace FiniteCurveComplexModel
variable (R : Type u) [Ring R] [Finite R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable (K : CochainComplex (DiscreteModuleCat R G) ℤ)

/-- The canonical upper truncation supplies cycles, not raw degree-two cochains. -/
abbrev window := (K.truncLE 2).sc 1

/-- Realize the three actual terms of this canonical truncation. -/
abbrev windowCochain :=
  (FiniteThreeTermModel.cochain R G (window R G K)).extend ComplexShape.embeddingUpNat

/-- Normalize the actual predecessor index in the short-complex window. -/
def windowZeroIso : (FiniteThreeTermModel.cochain R G (window R G K)).X 0 ≅
    (K.truncLE 2).X 0 :=
  (K.truncLE 2).XIsoOfEq ((ComplexShape.up ℤ).prev_eq'
    (show (ComplexShape.up ℤ).Rel 0 1 from by decide))

/-- Normalize the actual successor index in the short-complex window. -/
def windowTwoIso : (FiniteThreeTermModel.cochain R G (window R G K)).X 2 ≅
    (K.truncLE 2).X 2 :=
  (K.truncLE 2).XIsoOfEq ((ComplexShape.up ℤ).next_eq'
    (show (ComplexShape.up ℤ).Rel 1 2 from by decide))

/-- Explicit zero-extension comparison to the canonical truncation. In
degrees 0,1,2 it is the standard extension identification; elsewhere it is zero. -/
def windowMap : windowCochain R G K ⟶ K.truncLE 2 where
  f i := if h0 : i = 0 then
      ((windowCochain R G K).XIsoOfEq h0).hom ≫
      ((FiniteThreeTermModel.cochain R G (window R G K)).extendXIso
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).hom ≫ (windowZeroIso R G K).hom ≫
      ((K.truncLE 2).XIsoOfEq h0).inv
    else if h1 : i = 1 then
      ((windowCochain R G K).XIsoOfEq h1).hom ≫
      ((FiniteThreeTermModel.cochain R G (window R G K)).extendXIso
        ComplexShape.embeddingUpNat (i := 1) (i' := 1) rfl).hom ≫
      ((K.truncLE 2).XIsoOfEq h1).inv
    else if h2 : i = 2 then
      ((windowCochain R G K).XIsoOfEq h2).hom ≫
      ((FiniteThreeTermModel.cochain R G (window R G K)).extendXIso
        ComplexShape.embeddingUpNat (i := 2) (i' := 2) rfl).hom ≫ (windowTwoIso R G K).hom ≫
      ((K.truncLE 2).XIsoOfEq h2).inv
    else 0
  comm' := by sorry

/-- The finite subcomplex of the actual canonical truncation. -/
abbrev finiteCochain :=
  (FiniteThreeTermModel.cochain R G (FiniteThreeTermModel.model R G (window R G K))).extend
    ComplexShape.embeddingUpNat

/-- The actual comparison is inclusion of representatives/boundary lifts,
then the truncation inclusion. No desired comparison map is assumed. -/
def inclusion : finiteCochain R G K ⟶ K :=
  HomologicalComplex.extendMap
      (FiniteThreeTermModel.cochainInclusion R G (window R G K)) ComplexShape.embeddingUpNat ≫
    windowMap R G K ≫ K.ιTruncLE 2

/-- This comparison is a quasi-isomorphism precisely under the actual lower
support and upper cohomology bound; it is not asserted for arbitrary complexes. -/
theorem inclusion_quasiIso [K.IsStrictlyGE 0]
    (hvan : ∀ i : ℤ, 2 < i → IsZero (K.homology i)) : QuasiIso (inclusion R G K) := by sorry

/-- Finite homology of the given complex makes every term of this specific
three-term model finite. Source curve finiteness will discharge these classes. -/
theorem finite_terms [K.IsStrictlyGE 0]
    [Finite (K.homology 0).obj.V] [Finite (K.homology 1).obj.V] [Finite (K.homology 2).obj.V]
    (i : ℤ) : Finite ((finiteCochain R G K).X i).obj.V := by sorry

end FiniteCurveComplexModel
