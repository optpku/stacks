module

public import ReasLib.AlgebraicGeometry.Scheme.Variety
public import ReasLib.Topology.KrullDimension.Equidimensional
public import ReasLib.AlgebraicGeometry.WeilCohomology.MotivicRealization

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace WeilCohomology.MotivicRealization.ClassicalCore

/-- For a ℚ-linear strong monoidal realization of Chow motives over an algebraically
closed field, with coefficients in a characteristic-zero field and a coherent Tate
normalization, cohomological vanishing outside degrees `0` through `2 * d` together
with bijectivity of the top-degree trace is equivalent to vanishing in negative
degrees together with one-dimensional degree-zero cohomology, for every smooth
projective variety of dimension `d`. -/
theorem fullAxioms_iff
    {k : Type u} [Field k] [IsAlgClosed k]
    {F : Type v} [Field F] [CharZero F]
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)}
    [G.Linear ℚ] [G.Monoidal] (C : ClassicalCore G) :
    ((∀ (X : SchemeOverField k) [Variety X] [Smooth X.hom] [Projective X.hom]
        [EquidimensionalSpace X.left] (d : ℕ),
        topologicalKrullDim X.left = (d : WithBot ℕ∞) →
          ∀ i : ℤ, i < 0 ∨ 2 * (d : ℤ) < i →
            IsZero ((G.obj (ChowMotive.h X)) i)) ∧
      ∀ (X : SchemeOverField k) [Variety X] [Smooth X.hom] [Projective X.hom]
        [EquidimensionalSpace X.left] (d : ℕ)
        (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞)),
        Function.Bijective (C.integral X d hXdim).hom) ↔
    ((∀ (X : SchemeOverField k) [Variety X] [Smooth X.hom] [Projective X.hom]
        (i : ℤ), i < 0 → IsZero ((G.obj (ChowMotive.h X)) i)) ∧
      ∀ (X : SchemeOverField k) [Variety X] [Smooth X.hom] [Projective X.hom],
        Module.finrank F ((G.obj (ChowMotive.h X)) 0) = 1) := sorry

end WeilCohomology.MotivicRealization.ClassicalCore
