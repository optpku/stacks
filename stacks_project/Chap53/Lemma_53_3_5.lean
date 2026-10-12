/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.LinearSeries.Inequalities
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 53.3.5 (1): the dimension of a linear series on a proper curve with only constant
global functions is at most its degree. -/
@[stacks 0CCS] #check (AlgebraicGeometry.LinearSeries.dimension_le_degree :
  ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
    [AlgebraicGeometry.Curve X] [AlgebraicGeometry.IsProper X.hom]
    (hΓ : Function.Bijective (AlgebraicGeometry.Scheme.Hom.globalSectionsMap X.hom))
    {d r : ℕ},
    AlgebraicGeometry.LinearSeries X
      (AlgebraicGeometry.topologicalKrullDim_eq_one X).le d r → r ≤ d)

/- Lemma 53.3.5 (2): equality between the dimension and degree of a linear series on such a
curve forces the first cohomology of the structure sheaf to vanish. -/
@[stacks 0CCS] #check (AlgebraicGeometry.LinearSeries.structureSheafH1_isZero_of_dimension_eq_degree :
  ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
    [AlgebraicGeometry.Curve X] [AlgebraicGeometry.IsProper X.hom]
    (hΓ : Function.Bijective (AlgebraicGeometry.Scheme.Hom.globalSectionsMap X.hom))
    {d r : ℕ},
    AlgebraicGeometry.LinearSeries X
      (AlgebraicGeometry.topologicalKrullDim_eq_one X).le d r → r = d →
      IsZero (AlgebraicGeometry.Scheme.Hom.cohomology X.hom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1))

/- Lemma 53.3.5 (3): equality between the dimension and degree of a linear series on such a
curve forces the genus to be zero. -/
@[stacks 0CCS] #check (AlgebraicGeometry.LinearSeries.genus_eq_zero_of_dimension_eq_degree :
  ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
    [AlgebraicGeometry.Curve X] [AlgebraicGeometry.IsProper X.hom]
    (hΓ : Function.Bijective (AlgebraicGeometry.Scheme.Hom.globalSectionsMap X.hom))
    {d r : ℕ},
    AlgebraicGeometry.LinearSeries X
      (AlgebraicGeometry.topologicalKrullDim_eq_one X).le d r → r = d →
      AlgebraicGeometry.SchemeOverField.genus X
        (AlgebraicGeometry.topologicalKrullDim_eq_one X) hΓ = 0)
