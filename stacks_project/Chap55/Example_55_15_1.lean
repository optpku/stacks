module

public import ReasLib.AlgebraicGeometry.Scheme.Topology.RegularLocus
public import stacks_project.Chap55.Example_55_10_3_Conic
public import stacks_project.Chap55.Example_55_15_1_SumSquaresConic
public import stacks_project.Chap55.Lemma_55_12_4

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme.Hom CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.SumSquaresConic

/-- Example 55.15.1 (1): after coefficientwise extension to `ℂ[[X]]`, the real
sum-of-squares conic is isomorphic over the base to the split conic. -/
@[stacks 0CDL]
theorem complexBaseChange_iso_splitConic :
    Nonempty
      (Over.mk (pullback.snd (toSpec (PowerSeries ℝ) PowerSeries.X)
          (Spec.map (CommRingCat.ofHom complexPowerSeriesHom))) ≅
        Over.mk (SplitConic.toSpec (PowerSeries ℂ) PowerSeries.X)) := sorry

/-- Example 55.15.1 (2): the sum-of-squares conic over `ℝ[[X]]` is regular. -/
@[stacks 0CDL, instance]
instance realModel_regular : Scheme.Regular (model (PowerSeries ℝ) PowerSeries.X) := sorry

/-- Example 55.15.1 (3): the special fibre over `ℝ` is irreducible. -/
@[stacks 0CDL, instance]
instance realSpecialFiber_irreducible :
    IrreducibleSpace (specialFiber (PowerSeries ℝ) PowerSeries.X) := sorry

/-- Example 55.15.1 (4): the irreducible special fibre has a singular point. -/
@[stacks 0CDL]
theorem realSpecialFiber_singular :
    (Sing(specialFiber (PowerSeries ℝ) PowerSeries.X)).Nonempty := sorry

/-- Example 55.15.1 (5): the sum-of-squares conic is a minimal model over `ℝ[[X]]`. -/
@[stacks 0CDL, instance]
instance realModel_isMinimal :
    Scheme.Hom.IsMinimalModel (toSpec (PowerSeries ℝ) PowerSeries.X) := sorry

/-- The generic fibre of the real sum-of-squares conic. -/
abbrev realGenericFiber : SchemeOverField (LaurentSeries ℝ) :=
  genericFiber (PowerSeries ℝ) PowerSeries.X (LaurentSeries ℝ)

/-- The real generic fibre is a curve. -/
instance realGenericFiber_curve : Curve realGenericFiber := sorry

/-- The real generic fibre is smooth. -/
instance realGenericFiber_smooth : Smooth realGenericFiber.hom := sorry

/-- The real generic fibre is projective. -/
instance realGenericFiber_projective : Projective realGenericFiber.hom := sorry

/-- The real generic fibre is proper. -/
instance realGenericFiber_proper : IsProper realGenericFiber.hom := sorry

/-- The global functions on the real generic fibre are exactly the ground field. -/
theorem realGenericFiber_globalSections :
    Function.Bijective (Scheme.Hom.globalSectionsMap realGenericFiber.hom) := sorry

/-- The real conic model is Noetherian. -/
instance realModel_noetherian : IsNoetherian (model (PowerSeries ℝ) PowerSeries.X) := sorry

/-- The concrete regular model marked by the identity on its generic fibre. -/
def realRegularModel :
    RegularModel (PowerSeries ℝ) (LaurentSeries ℝ) realGenericFiber :=
  RegularModel.ofData (model (PowerSeries ℝ) PowerSeries.X)
    (toSpec (PowerSeries ℝ) PowerSeries.X) inferInstance inferInstance inferInstance
    inferInstance inferInstance (Iso.refl _)

/-- The structural morphism underlying `realRegularModel` is the concrete conic morphism. -/
theorem realRegularModel_base :
    realRegularModel.base = toSpec (PowerSeries ℝ) PowerSeries.X := sorry

/-- Example 55.15.1 (6): every minimal regular model of the real generic conic is
isomorphic to the concrete sum-of-squares model, compatibly with its generic-fibre marking. -/
@[stacks 0CDL]
theorem realRegularModel_unique
    (M : RegularModel (PowerSeries ℝ) (LaurentSeries ℝ) realGenericFiber)
    [IsMinimalModel M.base] :
    RegularModel.Isomorphic realRegularModel M := sorry

/-- Example 55.15.1 (7): the real generic conic has genus zero. -/
@[stacks 0CDL]
theorem realGenericFiber_genus_zero :
    SchemeOverField.genus realGenericFiber (topologicalKrullDim_eq_one realGenericFiber)
      realGenericFiber_globalSections = 0 := sorry

/-- Example 55.15.1 (8): the genus-zero real generic conic is not already a projective line
over `ℝ((X))`. -/
@[stacks 0CDL]
theorem realGenericFiber_not_iso_projectiveLine :
    ¬ Nonempty (realGenericFiber ≅ ProjectiveSpace.schemeOver (LaurentSeries ℝ) 1) := sorry

end AlgebraicGeometry.SumSquaresConic
