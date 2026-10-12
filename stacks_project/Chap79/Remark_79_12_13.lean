/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import stacks_project.Chap65.Example_65_14_2_Space
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap79.Lemma_79_12_2_FinitePart

/-!
# A finite origin morphism whose finite-part sheaf is not a scheme

For `Y = A¹_ℝ` and `f : Spec(ℂ) ⟶ Y` the morphism onto the `ℝ`-rational origin,
`f` is finite, but the finite-part sheaf `(X/Y)_fin` is isomorphic to the algebraic
space of Spaces, Example 65.14.2 associated to `ℝ ⊂ ℂ`, hence is not a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent

/-- `ℂ` is a free rank-two `ℝ`-algebra, hence a quadratic extension. -/
instance instIsQuadraticExtension_realComplex : Algebra.IsQuadraticExtension ℝ ℂ where
  finrank_eq_two' := Complex.finrank_real_complex

/-- Remark 79.12.13 (1): the morphism `f : Spec(ℂ) ⟶ A¹_ℝ` onto the `ℝ`-rational
origin of `Y = base ℝ` is finite. -/
@[stacks 04QJ, instance]
instance instIsFinite_originOver_realComplex :
    AlgebraicGeometry.IsFinite (originOver ℝ ℂ).hom := sorry

/-- The origin morphism `Spec(ℂ) ⟶ A¹_ℝ` is a morphism over `Y = base ℝ`. -/
theorem originOverToBaseAsOver_w :
    (originOver ℝ ℂ).hom ≫ (baseAsOver ℝ).hom = (originOver ℝ ℂ).hom :=
  sorry

/-- The origin morphism as an arrow of `Over (base ℝ)` from `Spec(ℂ)` to `A¹_ℝ`. -/
def originOverToBaseAsOver : originOver ℝ ℂ ⟶ baseAsOver ℝ :=
  Over.homMk ((originOver ℝ ℂ).hom : (originOver ℝ ℂ).left ⟶ (baseAsOver ℝ).left)
    originOverToBaseAsOver_w

/-- The origin morphism as a morphism of algebraic spaces over `A¹_ℝ`. -/
def originMorphism : ofOver (originOver ℝ ℂ) ⟶ ofOver (baseAsOver ℝ) :=
  ofOverMap originOverToBaseAsOver

/-- The finite-part sheaf `(X/Y)_fin` of the origin morphism `Spec(ℂ) ⟶ A¹_ℝ`. -/
def originFinitePart : Sheaf (Scheme.fppfTopology.over (base ℝ)) (Type 1) :=
  finitePartSheaf originMorphism

/-- Remark 79.12.13 (2): the finite-part sheaf `(X/Y)_fin` for `X = Spec(ℂ)` mapping
to the `ℝ`-rational origin of `Y = A¹_ℝ` is isomorphic to the algebraic space of
Spaces, Example 65.14.2 associated to `ℝ ⊂ ℂ`. -/
@[stacks 04QJ]
theorem originFinitePart_iso_sheafOfPoints :
    Nonempty (originFinitePart ≅ sheafOfPoints ℝ ℂ Complex.finrank_real_complex) :=
  sorry

/-- Remark 79.12.13 (3): `(X/Y)_fin` is not a scheme: it is not representable by an
object of `Over (base ℝ)` via `uliftYoneda.{1}`, even though `f` is finite. -/
@[stacks 04QJ]
theorem not_isRepresentable_originFinitePart :
    ¬ ∃ T : Over (base ℝ),
        Nonempty
          (originFinitePart ≅
            (Scheme.fppfTopology.over (base ℝ)).uliftYoneda.{1}.obj T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent
