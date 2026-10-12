/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.Nodal

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 53.21.1: an at-worst-nodal relative-dimension-one morphism admits an
étale-local chart around a singular fibre point by the standard model
`Spec(ℤ[u, v, a]/(u v - a))` over `Spec(ℤ[a])`; the displayed right square is
cartesian and the chart contains a point over the given point of `X`. -/
@[stacks 0CBY] #check (AlgebraicGeometry.Scheme.Hom.exists_etale_nodal_model :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S), [AtWorstNodal f] →
    ∀ (x : X) (hx : f.asFiber x ∈ Scheme.singularLocus (f.fiber (f x))),
    ∃ (U V W : Scheme.{u})
      (ux : U ⟶ X) (vs : V ⟶ S) (uw : U ⟶ W)
      (uv : U ⟶ V) (wv : W ⟶ V) (wm : W ⟶ NodalModel.model)
      (va : V ⟶ NodalModel.base),
      Etale ux ∧
        Etale vs ∧
          Etale uw ∧
            ux ≫ f = uv ≫ vs ∧
              uw ≫ wv = uv ∧
                IsPullback wv wm va NodalModel.toBase ∧
                  ∃ u : U, ux u = x)
