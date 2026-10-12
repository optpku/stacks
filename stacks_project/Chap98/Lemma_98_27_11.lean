/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Lemma_98_27_4_Functor
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Conditions
import Mathlib.Tactic.CrossRefAttribute

/-!
# Limit preservation of the Artin contraction functor

In Situation 98.27.1 the contraction functor on locally Noetherian schemes
over `S` preserves directed inverse limits of Noetherian affine schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.Scheme.Over

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- Lemma 98.27.11: In Situation 98.27.1 the functor `σ.functor` is limit
preserving: for a directed inverse limit `V = lim V_λ` of Noetherian affine
schemes over `S` we have `σ.functor(V) = colim σ.functor(V_λ)`, as
`IsColimit` of the canonical `σ.functor.mapCocone`. -/
@[stacks 0GI5]
theorem preservesDirectedAffineLimits (σ : ContractionSituation S) :
    Extension.PreservesDirectedAffineLimits (locallyNoetherian S) σ.functor :=
  sorry

/-- A directed inverse limit of affine objects of `locallyNoetherian S` is sent
by `σ.functor` to a colimit of types. -/
theorem preservesDirectedAffineLimits_mapCocone (σ : ContractionSituation S)
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ (locallyNoetherian S).FullSubcategory) (c : Cone D)
    (hc : IsLimit ((locallyNoetherian S).ι.mapCone c))
    (hD : ∀ i : I, IsAffine (D.obj i).obj.left)
    (hpt : IsAffine c.pt.obj.left) :
    Nonempty (IsColimit (σ.functor.mapCocone c.op)) :=
  sorry

/-- Limit preservation of `σ.functor` is equivalent to the directed affine
`IsColimit` condition on `σ.functor.mapCocone`. -/
theorem preservesDirectedAffineLimits_iff (σ : ContractionSituation S) :
    Extension.PreservesDirectedAffineLimits (locallyNoetherian S) σ.functor ↔
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ (locallyNoetherian S).FullSubcategory) (c : Cone D),
          IsLimit ((locallyNoetherian S).ι.mapCone c) →
          (∀ i : I, IsAffine (D.obj i).obj.left) →
          IsAffine c.pt.obj.left →
          Nonempty (IsColimit (σ.functor.mapCocone c.op)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
