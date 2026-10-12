/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.NodalModel.Standard
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal
public import ReasLib.AlgebraicGeometry.Scheme.Topology.RegularLocus

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- An at-worst-nodal relative-dimension-one morphism admits an étale-local chart
around every singular fibre point by `Spec(ℤ[u, v, a]/(u v - a))` over
`Spec(ℤ[a])`, with a cartesian model square and a chart point over the given point. -/
theorem exists_etale_nodal_model
    {X S : Scheme.{u}} (f : X ⟶ S) [AtWorstNodal f]
    (x : X)
    (hx : f.asFiber x ∈ Scheme.singularLocus (f.fiber (f x))) :
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
                  ∃ u : U, ux u = x := sorry

end AlgebraicGeometry.Scheme.Hom
