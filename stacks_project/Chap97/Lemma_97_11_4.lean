/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap97.Lemma_97_11_4_RelativeHom
public import stacks_project.Chap97.Lemma_97_11_4_Restriction

/-!
# Cartesian square for restriction of scalars of algebraic spaces

The square relating `Res_{Z/B}(X)` to `Mor_B(Z, X)` over the identity section of
`Z` is cartesian in fppf sheaves on schemes over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars

/-- Lemma 97.11.4: let `S` be a scheme and let `X ⟶ Z ⟶ B` be morphisms of
algebraic spaces over `S`. The square of fppf sheaves on `Over S` with vertices
`RelativeHom.sheaf g (f ≫ g)`, `RelativeHom.sheaf g g`, `sheaf f g`, and
`uliftSheafOfPoints B`, whose right vertical map is the identity section of `Z`,
is cartesian. -/
@[stacks 05YE]
theorem isPullback {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z)
    (g : Z ⟶ B) :
    IsPullback (toRelativeHom f g) (toBase f g) (RelativeHom.postcomp f g)
      (RelativeHom.idSection g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars
