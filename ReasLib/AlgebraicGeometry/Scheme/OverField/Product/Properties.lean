/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Product

/-!
# Projective products over a field

This file records projectivity of products of projective schemes over a field.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- The product over a field of two projective schemes is projective. -/
instance instProjectiveProd
    {X Y : SchemeOverField k} [Projective X.hom] [Projective Y.hom] :
    Projective (X ⨯ Y).hom := sorry

end AlgebraicGeometry
