/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
public import stacks_project.Chap105.Definition_105_4_3_Smooth
public import stacks_project.Chap105.Definition_105_5_1_Moduli
public import stacks_project.Chap105.Lemma_105_4_1_Key_fact

/-!
# Introductory algebraic-stack condition for `M_{1,1}`

This file owns the source-facing property that the moduli stack of elliptic
curves is an algebraic stack in the sense of the étale descent, key fact, and
smooth surjective scheme atlas of Definition 105.5.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.EllipticCurve.Moduli

/-- A 1-morphism `S ⟶ M_{1,1}` is surjective on schemes when every scheme
representing a 2-fibre product with a test morphism `S' ⟶ M_{1,1}` has
surjective projection `S ×_{M_{1,1}} S' ⟶ S'`. -/
def surjectiveOnSchemes {U : Over specInt.{u}}
    (p : GroupoidsOver.slice U ⟶ moduli.{u}) : Prop :=
  ∀ ⦃S' : Over specInt.{u}⦄ (g : GroupoidsOver.slice S' ⟶ moduli.{u})
    (W : Over specInt.{u}) (π : W ⟶ S'),
    Groupoids.Hom.RepresentsSchemeBaseChange p g W π →
      AlgebraicGeometry.Surjective π.left

/-- Unfold scheme-level surjectivity of a 1-morphism into `M_{1,1}` to the
representing-projection criterion. -/
theorem surjectiveOnSchemes_iff {U : Over specInt.{u}}
    (p : GroupoidsOver.slice U ⟶ moduli.{u}) :
    surjectiveOnSchemes p ↔
      ∀ ⦃S' : Over specInt.{u}⦄ (g : GroupoidsOver.slice S' ⟶ moduli.{u})
        (W : Over specInt.{u}) (π : W ⟶ S'),
        Groupoids.Hom.RepresentsSchemeBaseChange p g W π →
          AlgebraicGeometry.Surjective π.left := sorry

/-- The moduli stack `M_{1,1}` is an algebraic stack in the introductory sense
when it has descent for objects in the étale topology on `Sch`, the key fact
holds, and it admits a surjective smooth morphism from a scheme. -/
class IsAlgebraicStack : Prop where
  /-- Descent for objects on the étale site of `Over (Spec ℤ)`. -/
  descent :
    IsStack.InGroupoids (Scheme.etaleTopology.over specInt.{u}) moduli.{u}.p
  /-- The key fact: 2-fibre products of morphisms from schemes into `M_{1,1}`
  are representable by schemes. -/
  keyFact :
    FiberedCategoryOver.Groupoids.relativelyRepresentable
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} moduli.{u})
  /-- There exists a scheme `S` and a 1-morphism `S ⟶ M_{1,1}` that is smooth
  on schemes and whose representing projections are surjective. -/
  existsSmoothSurjectiveAtlas :
    ∃ (U : Over specInt.{u}) (p : GroupoidsOver.slice U ⟶ moduli.{u}),
      Groupoids.Hom.SmoothOnSchemes p ∧
        ∀ ⦃S' : Over specInt.{u}⦄ (g : GroupoidsOver.slice S' ⟶ moduli.{u})
          (W : Over specInt.{u}) (π : W ⟶ S'),
          Groupoids.Hom.RepresentsSchemeBaseChange p g W π →
            AlgebraicGeometry.Surjective π.left

/-- An introductory algebraic stack of elliptic curves is a stack in groupoids
on the étale site of `Over (Spec ℤ)`. -/
instance instIsStackInGroupoids [h : IsAlgebraicStack.{u}] :
    IsStack.InGroupoids (Scheme.etaleTopology.over specInt.{u}) moduli.{u}.p :=
  h.descent

/-- The three defining clauses of the introductory algebraic-stack condition on
`M_{1,1}`. -/
theorem IsAlgebraicStack.spec [IsAlgebraicStack] :
    IsStack.InGroupoids (Scheme.etaleTopology.over specInt.{u}) moduli.{u}.p ∧
      FiberedCategoryOver.Groupoids.relativelyRepresentable
          (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} moduli.{u}) ∧
        ∃ (U : Over specInt.{u}) (p : GroupoidsOver.slice U ⟶ moduli.{u}),
          Groupoids.Hom.SmoothOnSchemes p ∧
            ∀ ⦃S' : Over specInt.{u}⦄ (g : GroupoidsOver.slice S' ⟶ moduli.{u})
              (W : Over specInt.{u}) (π : W ⟶ S'),
              Groupoids.Hom.RepresentsSchemeBaseChange p g W π →
                AlgebraicGeometry.Surjective π.left := sorry

/-- The introductory algebraic-stack condition on `M_{1,1}` is equivalent to
étale descent for objects, the key fact, and a surjective smooth scheme
atlas. -/
theorem IsAlgebraicStack.iff :
    IsAlgebraicStack ↔
      IsStack.InGroupoids (Scheme.etaleTopology.over specInt.{u}) moduli.{u}.p ∧
        FiberedCategoryOver.Groupoids.relativelyRepresentable
            (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} moduli.{u}) ∧
          ∃ (U : Over specInt.{u}) (p : GroupoidsOver.slice U ⟶ moduli.{u}),
            Groupoids.Hom.SmoothOnSchemes p ∧
              ∀ ⦃S' : Over specInt.{u}⦄ (g : GroupoidsOver.slice S' ⟶ moduli.{u})
                (W : Over specInt.{u}) (π : W ⟶ S'),
                Groupoids.Hom.RepresentsSchemeBaseChange p g W π →
                  AlgebraicGeometry.Surjective π.left := sorry

/-- The key fact at the stack layer is equivalent to representability of the
fibre-product functor of any two geometric elliptic curves. -/
theorem keyFact_iff :
    FiberedCategoryOver.Groupoids.relativelyRepresentable
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} moduli.{u}) ↔
      ∀ {S S' : Scheme.{u}} (E : Over S) (zero : S ⟶ E.left)
        (E' : Over S') (zero' : S' ⟶ E'.left)
        [IsEllipticCurve E zero] [IsEllipticCurve E' zero'],
        (functor E zero E' zero').IsRepresentable := sorry

/-- Smoothness of a classifying 1-morphism is equivalent to relative
representability together with smoothness of every representing projection
`S ×_{M_{1,1}} S' ⟶ S'`. -/
theorem classifying_smooth_iff {U : Over specInt.{u}} (E : Over U.left)
    (zero : U.left ⟶ E.left) [IsEllipticCurve E zero] :
    Groupoids.Hom.SmoothOnSchemes (classifying U E zero) ↔
      FiberedCategoryOver.Groupoids.relativelyRepresentable
          (classifying U E zero) ∧
        ∀ ⦃S' : Over specInt.{u}⦄ (g : GroupoidsOver.slice S' ⟶ moduli.{u})
          (W : Over specInt.{u}) (π : W ⟶ S'),
          Groupoids.Hom.RepresentsSchemeBaseChange (classifying U E zero) g W π →
            AlgebraicGeometry.Smooth π.left := sorry

/-- Surjectivity of a classifying 1-morphism is equivalent to surjectivity of
every representing projection `S ×_{M_{1,1}} S' ⟶ S'`. -/
theorem classifying_surjective_iff {U : Over specInt.{u}} (E : Over U.left)
    (zero : U.left ⟶ E.left) [IsEllipticCurve E zero] :
    surjectiveOnSchemes (classifying U E zero) ↔
      ∀ ⦃S' : Over specInt.{u}⦄ (g : GroupoidsOver.slice S' ⟶ moduli.{u})
        (W : Over specInt.{u}) (π : W ⟶ S'),
        Groupoids.Hom.RepresentsSchemeBaseChange (classifying U E zero) g W π →
          AlgebraicGeometry.Surjective π.left := sorry

end AlgebraicGeometry.EllipticCurve.Moduli
