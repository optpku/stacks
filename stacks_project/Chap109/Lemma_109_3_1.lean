/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap109.Lemma_109_3_1_Classifying
public import stacks_project.Chap109.Lemma_109_3_1_Family

/-!
# Lemma 109.3.1

The Hom-category Mor(T, Curves) of an algebraic space T is the groupoid of
families of curves over T. The written identification
Mor_B(T, B-Curves) = Mor(T, Curves) is the 2-fibre product of
CurvesGroupoidsOver.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces
open Functor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace Curves

/-- Lemma 109.3.1: let `T ⟶ B` be a morphism of algebraic spaces. The category
`Mor_B(T, B-Curves) = Mor(T, Curves)` is the category of families of curves
over `T`. Here `Mor(T, Curves)` is the Hom-category of cartesian functors
`𝒮_T ⟶ Curves` over `Sch/S`, identified with the groupoid `FamilyOver T` of
morphisms of algebraic spaces `X ⟶ T` that are flat, proper, of finite
presentation, and of relative dimension at most `1`. The equality
`Mor_B(T, B-Curves) = Mor(T, Curves)` is the product description of
`B-Curves` as the 2-fibre product `CurvesGroupoidsOver`. -/
@[stacks 0DMK]
instance classifying.instIsEquivalence {S : Scheme.{u}} (T : AlgebraicSpace S) :
    (classifying T).IsEquivalence :=
  sorry

end Curves
end AlgebraicGeometry.AlgebraicSpace.Spaces
