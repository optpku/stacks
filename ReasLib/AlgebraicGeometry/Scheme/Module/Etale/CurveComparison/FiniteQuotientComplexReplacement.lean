module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteQuotientCoefficientResolution
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteProjectiveComplexReplacement
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactDegreePlacement

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
noncomputable section
universe u v

namespace FiniteQuotientComplexReplacement
variable (R : Type u) (G : Type v) [Ring R]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (K : CochainComplex (DiscreteModuleCat R G) ℤ)
variable [Finite (K.X 0).obj.V] [Finite (K.X 1).obj.V] [Finite (K.X 2).obj.V]
variable [K.IsStrictlyGE 0] [K.IsStrictlyLE 2]

abbrev quotient := G ⧸ (FiniteComplexQuotient.commonKernel R G K).toSubgroup
abbrev algebra := MonoidAlgebra R (quotient R G K)

instance toFunctor_additive : (NoncommGroupAlgebraModule.toFunctor R (quotient R G K)).Additive := by
  sorry

/-- Descend the given differential, then apply the actual group-algebra action. -/
def algebraCochain := ((NoncommGroupAlgebraModule.toFunctor R (quotient R G K)).mapHomologicalComplex
  (ComplexShape.up ℤ)).obj (FiniteComplexQuotient.complex R G K)

/-- Reverse the upper-bounded cochain complex using exactly degree 2-n. -/
def algebraChain : ChainComplex (ModuleCat.{max u v} (algebra R G K)) ℕ :=
  ChainComplex.of (fun n ↦ (algebraCochain R G K).X (2 - (n : ℤ)))
    (fun n ↦ (algebraCochain R G K).d (2 - ((n + 1 : ℕ) : ℤ)) (2 - (n : ℤ)))
    (by intro n; exact (algebraCochain R G K).d_comp_d _ _ _)

/-- Fixed finite quotient realization; no ambient projectivity claim. -/
def realization := NoncommGroupAlgebraModule.fromFunctor R (quotient R G K) ⋙
  OpenQuotientInflation.functor R G (FiniteComplexQuotient.commonKernel R G K)

instance realization_additive : (realization R G K).Additive := by sorry

/-- Actual compatible-pair free replacement, inflated and placed in degree 2-n. -/
def complex := (((realization R G K).mapHomologicalComplex (ComplexShape.down ℕ)).obj
  (FiniteProjectiveComplexReplacement.complex (algebra R G K) (algebraChain R G K))).extend
    CompactRepresentation.curveDegreeEmbedding

/-- Recover each descended coefficient using the literal group-algebra recovery. -/
def termIso (i : ℤ) : (realization R G K).obj ((algebraCochain R G K).X i) ≅ K.X i :=
  (OpenQuotientInflation.functor R G (FiniteComplexQuotient.commonKernel R G K)).mapIso
    (NoncommGroupAlgebraModule.actionIso R (quotient R G K)
      ((FiniteComplexQuotient.complex R G K).X i)) ≪≫
    ObjectProperty.isoMk _ (Action.mkIso (Iso.refl (K.X i).obj.V) (fun _ ↦ by sorry))

/-- Undo only the degree embedding. All nonzero components are specified identity/recovery maps. -/
def recovery : (((realization R G K).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (algebraChain R G K)).extend CompactRepresentation.curveDegreeEmbedding ⟶ K where
  f i := if h : i ≤ 2 then
      ((((realization R G K).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (algebraChain R G K)).extendXIso CompactRepresentation.curveDegreeEmbedding
          (i := (2 - i).toNat) (i' := i) (by sorry)).hom ≫
      (termIso R G K (2 - ((2 - i).toNat : ℤ))).hom ≫
      (K.XIsoOfEq (by omega : 2 - ((2 - i).toNat : ℤ) = i)).hom
    else 0
  comm' := by sorry

/-- The explicit augmentation, degree transport, and recovery into the original complex. -/
def toOriginal : complex R G K ⟶ K :=
  HomologicalComplex.extendMap
    (((realization R G K).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (FiniteProjectiveComplexReplacement.toOriginal (algebra R G K) (algebraChain R G K)))
    CompactRepresentation.curveDegreeEmbedding ≫ recovery R G K

theorem toOriginal_quasiIso : QuasiIso (toOriginal R G K) := by sorry

/-- Projectivity is over R, not in the category of all discrete G-modules. -/
theorem term_projective (i : ℤ) : Module.Projective R ((complex R G K).X i).obj.V := by sorry

theorem term_finite [Finite R] (i : ℤ) : Finite ((complex R G K).X i).obj.V := by sorry

end FiniteQuotientComplexReplacement
