module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Pointwise étale scheme morphisms

This file defines étaleness at a point using compatible affine neighborhoods
and the induced map on coordinate rings.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X S : Scheme.{u}}

/-- A scheme morphism is étale at `x` when there are compatible affine neighborhoods of `x`
and its image for which the induced map on coordinate rings is étale. -/
def EtaleAt (f : X ⟶ S) (x : X) : Prop :=
  ∃ V : S.affineOpens, ∃ U : X.affineOpens,
    x ∈ (U : X.Opens) ∧ ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
      (f.appLE (V : S.Opens) (U : X.Opens) e).hom.Etale

/-- A scheme morphism is etale at a point exactly when the point has an affine neighborhood
mapping into an affine open of the target such that the induced map on coordinate rings is
etale. -/
theorem etaleAt_iff_exists_affineOpen (f : X ⟶ S) (x : X) :
    f.EtaleAt x ↔
      ∃ V : S.affineOpens, ∃ U : X.affineOpens,
        x ∈ (U : X.Opens) ∧ ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
          (f.appLE (V : S.Opens) (U : X.Opens) e).hom.Etale := sorry

/-- A scheme morphism is etale exactly when it is etale at every point of its source. -/
theorem etale_iff_forall_etaleAt (f : X ⟶ S) :
    Etale f ↔ ∀ x : X, f.EtaleAt x := sorry

end Scheme.Hom
end AlgebraicGeometry
