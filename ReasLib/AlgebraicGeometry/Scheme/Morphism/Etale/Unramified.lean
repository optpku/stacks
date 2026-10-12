/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.LocalCriterion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat

/-!
# Étale and G-unramified morphisms

This file relates étaleness of scheme morphisms to flatness and G-unramifiedness,
both at a point and globally.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X S : Scheme.{u}}

/-- A scheme morphism is étale at a source point if and only if it is flat and
G-unramified at that point. -/
theorem etaleAt_iff_flatAt_and_gUnramifiedAt (f : X ⟶ S) (x : X) :
    f.EtaleAt x ↔ Scheme.Hom.flatAt f x ∧ f.GUnramifiedAt x := sorry

end Scheme.Hom

namespace Etale

/-- A scheme morphism is étale if and only if it is flat and G-unramified. -/
theorem iff_flat_and_gUnramified {X S : Scheme.{u}} (f : X ⟶ S) :
    Etale f ↔ Flat f ∧ GUnramified f := sorry

end Etale

end AlgebraicGeometry
