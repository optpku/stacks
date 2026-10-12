/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Transitivity
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Descent

/-!
# Pointwise flatness under base change

This file compares pointwise flatness across cartesian squares of schemes with a flat base
morphism.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- In a cartesian square over a flat base morphism, pointwise flatness is preserved and
reflected. -/
theorem flatAt_iff_of_isPullback_of_flat_base
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (hcart : IsPullback g' f' f g) [Flat g] (x' : X') :
    Scheme.Hom.flatAt f' x' ↔ Scheme.Hom.flatAt f (g' x') := sorry

end AlgebraicGeometry.Scheme.Hom
