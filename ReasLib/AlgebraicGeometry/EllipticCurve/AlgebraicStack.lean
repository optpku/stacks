module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
public import ReasLib.AlgebraicGeometry.GroupoidsOver.SmoothOnSchemes
public import ReasLib.AlgebraicGeometry.EllipticCurve.Moduli
public import ReasLib.AlgebraicGeometry.EllipticCurve.FiberProduct

/-!
# Algebraic-stack condition for the moduli of elliptic curves

The condition consists of étale descent, a scheme-representable diagonal,
and a smooth surjective scheme atlas.
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
          AlgebraicGeometry.Surjective π.left := Iff.rfl

/-- The moduli stack `M_{1,1}` is an algebraic stack in the introductory sense
when it has descent for objects in the étale topology on `Sch`, the key fact
holds, and it admits a surjective smooth morphism from a scheme. -/
def IsAlgebraicStack : Prop :=
  IsStack.InGroupoids (Scheme.etaleTopology.over specInt.{u}) moduli.{u}.p ∧
    FiberedCategoryOver.Groupoids.relativelyRepresentable
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} moduli.{u}) ∧
      ∃ (U : Over specInt.{u}) (p : GroupoidsOver.slice U ⟶ moduli.{u}),
        Groupoids.Hom.SmoothOnSchemes p ∧
          ∀ ⦃S' : Over specInt.{u}⦄ (g : GroupoidsOver.slice S' ⟶ moduli.{u})
            (W : Over specInt.{u}) (π : W ⟶ S'),
            Groupoids.Hom.RepresentsSchemeBaseChange p g W π →
              AlgebraicGeometry.Surjective π.left

/-- The three defining clauses of the introductory algebraic-stack condition on
`M_{1,1}`. -/
theorem IsAlgebraicStack.spec (h : IsAlgebraicStack.{u}) :
    IsStack.InGroupoids (Scheme.etaleTopology.over specInt.{u}) moduli.{u}.p ∧
      FiberedCategoryOver.Groupoids.relativelyRepresentable
          (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} moduli.{u}) ∧
        ∃ (U : Over specInt.{u}) (p : GroupoidsOver.slice U ⟶ moduli.{u}),
          Groupoids.Hom.SmoothOnSchemes p ∧
            ∀ ⦃S' : Over specInt.{u}⦄ (g : GroupoidsOver.slice S' ⟶ moduli.{u})
              (W : Over specInt.{u}) (π : W ⟶ S'),
              Groupoids.Hom.RepresentsSchemeBaseChange p g W π →
                AlgebraicGeometry.Surjective π.left := h

/-- The introductory algebraic-stack condition on `M_{1,1}` is equivalent to
étale descent for objects, the key fact, and a surjective smooth scheme
atlas. -/
theorem IsAlgebraicStack.iff :
    IsAlgebraicStack.{u} ↔
      IsStack.InGroupoids (Scheme.etaleTopology.over specInt.{u}) moduli.{u}.p ∧
        FiberedCategoryOver.Groupoids.relativelyRepresentable
            (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} moduli.{u}) ∧
          ∃ (U : Over specInt.{u}) (p : GroupoidsOver.slice U ⟶ moduli.{u}),
            Groupoids.Hom.SmoothOnSchemes p ∧
              ∀ ⦃S' : Over specInt.{u}⦄ (g : GroupoidsOver.slice S' ⟶ moduli.{u})
                (W : Over specInt.{u}) (π : W ⟶ S'),
                Groupoids.Hom.RepresentsSchemeBaseChange p g W π →
                  AlgebraicGeometry.Surjective π.left := Iff.rfl

/-- The key fact at the stack layer is equivalent to representability of the
fibre-product functor of any two geometric elliptic curves. -/
theorem keyFact_iff :
    FiberedCategoryOver.Groupoids.relativelyRepresentable
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} moduli.{u}) ↔
      ∀ {S S' : Scheme.{u}} (E : Over S) (zero : S ⟶ E.left)
        (E' : Over S') (zero' : S' ⟶ E'.left)
        [IsEllipticCurve E zero] [IsEllipticCurve E' zero'],
        (functor E zero E' zero').IsRepresentable := sorry

end AlgebraicGeometry.EllipticCurve.Moduli
