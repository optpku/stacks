module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.NaiveCotangent.Homology
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree

/-!
# Smooth morphisms of algebraic spaces versus the naive cotangent complex

A morphism of algebraic spaces is smooth if and only if it is locally of finite
presentation, the degree `-1` homology of its naive cotangent complex vanishes,
and its sheaf of relative differentials is finite locally free.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Smooth

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- A morphism of algebraic spaces is smooth if and only if it is locally of
finite presentation, the degree `-1` homology of its naive cotangent complex
vanishes, and its sheaf of relative differentials is finite locally free. -/
theorem iff_naiveCotangent :
    Smooth f ↔
      LocallyOfFinitePresentation f ∧
        IsZero ((NL[f]).homology (-1)) ∧ (Ω[f]).IsFiniteLocallyFree :=
  sorry

/-- A smooth morphism of algebraic spaces has vanishing degree `-1`
naive-cotangent homology. -/
theorem homology_negOne_isZero [Smooth f] :
    IsZero ((NL[f]).homology (-1)) :=
  ((iff_naiveCotangent f).mp inferInstance).2.1

/-- A locally finitely presented morphism of algebraic spaces with vanishing
degree `-1` naive-cotangent homology and finite locally free relative
differentials is smooth. -/
theorem of_naiveCotangent [LocallyOfFinitePresentation f]
    (h : IsZero ((NL[f]).homology (-1))) [(Ω[f]).IsFiniteLocallyFree] :
    Smooth f :=
  (iff_naiveCotangent f).mpr ⟨inferInstance, h, inferInstance⟩

end AlgebraicGeometry.AlgebraicSpace.Smooth
