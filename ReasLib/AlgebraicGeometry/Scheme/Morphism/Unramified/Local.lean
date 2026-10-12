/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic

/-!
# Pointwise unramified scheme morphisms

This file owns the affine-neighborhood unramified and G-unramified predicates,
their global characterizations, and their quasi-finiteness consequences.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

namespace Scheme.Hom

/-- A scheme morphism is unramified at `x` when it is unramified on compatible affine source and
target neighborhoods, with the source neighborhood containing `x`. -/
def UnramifiedAt (f : X ⟶ S) (x : X) : Prop :=
  ∃ V : S.affineOpens, ∃ U : X.affineOpens,
    x ∈ U.1 ∧ ∃ e : U.1 ≤ f ⁻¹ᵁ V.1,
      Unramified (f.resLE V.1 U.1 e)

/-- Pointwise unramifiedness is equivalent to its affine-neighborhood witness condition. -/
theorem unramifiedAt_iff (f : X ⟶ S) (x : X) :
    f.UnramifiedAt x ↔
      ∃ V : S.affineOpens, ∃ U : X.affineOpens,
        x ∈ U.1 ∧ ∃ e : U.1 ≤ f ⁻¹ᵁ V.1,
          Unramified (f.resLE V.1 U.1 e) := sorry

/-- A scheme morphism is G-unramified at `x` when it is G-unramified on compatible affine source
and target neighborhoods, with the source neighborhood containing `x`. -/
def GUnramifiedAt (f : X ⟶ S) (x : X) : Prop :=
  ∃ V : S.affineOpens, ∃ U : X.affineOpens,
    x ∈ U.1 ∧ ∃ e : U.1 ≤ f ⁻¹ᵁ V.1,
      GUnramified (f.resLE V.1 U.1 e)

/-- Pointwise G-unramifiedness is equivalent to its affine-neighborhood witness condition. -/
theorem gUnramifiedAt_iff (f : X ⟶ S) (x : X) :
    f.GUnramifiedAt x ↔
      ∃ V : S.affineOpens, ∃ U : X.affineOpens,
        x ∈ U.1 ∧ ∃ e : U.1 ≤ f ⁻¹ᵁ V.1,
          GUnramified (f.resLE V.1 U.1 e) := sorry

/-- A scheme morphism is unramified exactly when it is unramified at every source point. -/
theorem unramified_iff_forall_unramifiedAt (f : X ⟶ S) :
    Unramified f ↔ ∀ x : X, f.UnramifiedAt x := sorry

/-- A scheme morphism is G-unramified exactly when it is G-unramified at every source point. -/
theorem gUnramified_iff_forall_gUnramifiedAt (f : X ⟶ S) :
    GUnramified f ↔ ∀ x : X, f.GUnramifiedAt x := sorry

end Scheme.Hom

namespace Scheme.Hom

/-- A pointwise unramified morphism is quasi-finite at that point. -/
theorem UnramifiedAt.quasiFiniteAt
    {f : X ⟶ S} {x : X} (h : f.UnramifiedAt x) :
    f.QuasiFiniteAt x := sorry

end Scheme.Hom

/-- An unramified morphism is locally quasi-finite. -/
instance unramified_locallyQuasiFinite
    (f : X ⟶ S) [Unramified f] :
    LocallyQuasiFinite f := sorry

namespace Unramified

/-- An unramified morphism is locally quasi-finite. -/
theorem locallyQuasiFinite
    {f : X ⟶ S} (h : Unramified f) :
    LocallyQuasiFinite f := sorry

end Unramified

end AlgebraicGeometry
