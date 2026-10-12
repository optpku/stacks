/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution
public import ReasLib.Algebra.Homology.DerivedCategory.KProjective.Bounded
public import ReasLib.Algebra.Homology.HomotopyCategory.QuasiIso.Bounded
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pointwise Computation by Bounded-Above K-Projectives

This leaf exposes the proposition-valued `K⁻` computation API. Unlike the unbounded
`Functor.KProjective` leaf, it deliberately does not choose inverse morphisms through the
currently deferred bounded localization-model proof.
-/

open CategoryTheory Limits ComplexShape

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.KProjective.Bounded

variable {𝒜 : Type u₁} {𝒟 : Type u₂}
  [Category.{v₁} 𝒜] [Abelian 𝒜] [Category.{v₂} 𝒟]

/-- Localizing bounded-above homotopy complexes at quasi-isomorphisms is
bijective on maps from a bounded-above K-projective object. -/
@[stacks 064B]
theorem Localization.map_bijective
    (P L : HomotopyCategory.Minus 𝒜) [CochainComplex.IsKProjective P.obj.as] :
    Function.Bijective
      ((MorphismProperty.Q (HomotopyCategory.Minus.quasiIso 𝒜)).map :
        (P ⟶ L) →
          ((MorphismProperty.Q (HomotopyCategory.Minus.quasiIso 𝒜)).obj P ⟶
            (MorphismProperty.Q (HomotopyCategory.Minus.quasiIso 𝒜)).obj L)) := by
  have boundedLeftOrthogonal : (HomotopyCategory.Minus.acyclic 𝒜).leftOrthogonal P := by
    intro object morphism acyclic
    apply (HomotopyCategory.minus 𝒜).ι.map_injective
    change morphism.hom = 0
    exact (CochainComplex.IsKProjective.leftOrthogonal P.obj.as) morphism.hom acyclic
  rw [← HomotopyCategory.Minus.acyclic_trW_eq_quasiIso 𝒜]
  exact boundedLeftOrthogonal.map_bijective_of_isTriangulated _ L

/-- A bounded-above K-projective homotopy object computes the pointwise left-derived value of
every functor out of `K⁻(𝒜)`. -/
@[stacks 064B "pointwise left-derived computation"]
instance computesAt
    (F : HomotopyCategory.Minus 𝒜 ⥤ 𝒟) (P : HomotopyCategory.Minus 𝒜)
    [CochainComplex.IsKProjective P.obj.as] :
    LeftDerived.ComputesAt F (HomotopyCategory.Minus.quasiIso 𝒜) P := sorry

/-- A bounded-above cochain complex of projectives computes the pointwise left-derived value
after passing to the bounded-above homotopy category. This cochain-level form avoids a
caller-side K-projectivity bridge. -/
@[stacks 064B "pointwise left-derived computation"]
theorem computesAtOfProjectiveMinus
    (F : HomotopyCategory.Minus 𝒜 ⥤ 𝒟) (P : CochainComplex.ProjectiveMinus 𝒜) :
    LeftDerived.ComputesAt F (HomotopyCategory.Minus.quasiIso 𝒜)
      ((HomotopyCategory.Minus.quotient 𝒜).obj P) := sorry

end CategoryTheory.Functor.KProjective.Bounded
