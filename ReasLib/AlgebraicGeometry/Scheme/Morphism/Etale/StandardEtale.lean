module

public import Mathlib.RingTheory.Unramified.LocalStructure
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Basic

/-!
# Standard etale neighborhoods of scheme morphisms

This file relates etaleness at a point to standard etale maps on affine
coordinate rings over a fixed affine neighborhood in the target.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- The coordinate-ring map induced by `f` from an affine open `U` to an affine open `V`
of the target is standard etale. -/
def IsStandardEtaleOver (f : X ⟶ S) (V : S.affineOpens) (U : X.affineOpens) : Prop :=
  ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
    @Algebra.IsStandardEtale Γ(S, (V : S.Opens)) Γ(X, (U : X.Opens)) _ _
      (f.appLE (V : S.Opens) (U : X.Opens) e).hom.toAlgebra

/-- An affine coordinate map is standard etale over `V` exactly when its containment in the
preimage of `V` induces a standard etale algebra structure. -/
theorem isStandardEtaleOver_iff
    (f : X ⟶ S) (V : S.affineOpens) (U : X.affineOpens) :
    f.IsStandardEtaleOver V U ↔
      ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
        @Algebra.IsStandardEtale Γ(S, (V : S.Opens)) Γ(X, (U : X.Opens)) _ _
          (f.appLE (V : S.Opens) (U : X.Opens) e).hom.toAlgebra :=
  Iff.rfl

/-- A scheme morphism is etale at a point exactly when the point has an affine neighborhood
whose coordinate-ring map over a fixed affine target neighborhood is standard etale. -/
theorem etaleAt_iff_exists_affineOpen_over_isStandardEtale
    (x : X) (V : S.affineOpens) (hxV : f x ∈ (V : S.Opens)) :
    f.EtaleAt x ↔
      ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        f.IsStandardEtaleOver V U := sorry

end Scheme.Hom
end AlgebraicGeometry
