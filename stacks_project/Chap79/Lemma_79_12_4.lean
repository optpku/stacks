/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap79.«79_12_0_1_FinitePart»

/-!
# Closedness of finite-part open subspaces

If `f : X ⟶ Y` is a separated morphism of algebraic spaces, then the open
subspace `Z` in a finite-part pair `(a, Z)` is closed in `T ×_Y X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

/-- Lemma 79.12.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `T` be an algebraic space over `S`, and let
`(a, Z)` be a pair as in 79.12.0.1. If `f` is separated, then `Z` is closed
in `T ×_Y X`. -/
@[stacks 04PH, instance]
instance instIsClosedImmersion_ι {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    {f : X ⟶ Y} [Separated f] (p : FinitePart f T) :
    IsClosedImmersion p.Z.ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePart
