/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap76.Definition_76_7_2_Differentials
public import stacks_project.Chap76.Definition_76_21_1_NaiveCotangent

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
  sorry

/-- A locally finitely presented morphism of algebraic spaces with vanishing
degree `-1` naive-cotangent homology and finite locally free relative
differentials is smooth. -/
theorem of_naiveCotangent [LocallyOfFinitePresentation f]
    (h : IsZero ((NL[f]).homology (-1))) [(Ω[f]).IsFiniteLocallyFree] :
    Smooth f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Smooth
