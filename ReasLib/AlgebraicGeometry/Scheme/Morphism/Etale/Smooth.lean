/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified

/-!
# Pointwise smooth and étale scheme morphisms

This file relates smoothness, étaleness, and unramifiedness at a point using
compatible affine neighborhoods and induced maps on coordinate rings.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X S : Scheme.{u}}

/-- Etaleness at a point implies smoothness at that point. -/
theorem SmoothAt.of_etaleAt
    {f : X ⟶ S} {x : X} (h : f.EtaleAt x) :
    f.SmoothAt x := sorry

/-- Etaleness at a point is equivalent to smoothness and unramifiedness at that point. -/
theorem etaleAt_iff_smoothAt_and_unramifiedAt
    (f : X ⟶ S) (x : X) :
    f.EtaleAt x ↔ f.SmoothAt x ∧ f.UnramifiedAt x := sorry

end Scheme.Hom
end AlgebraicGeometry
