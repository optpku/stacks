/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion

/-!
# Open, closed, and locally closed subspaces of algebraic spaces

An open, closed, or locally closed subspace of an algebraic space `F` is an algebraic
space over the same base together with an inclusion into `F` that is an open immersion,
closed immersion, or immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An open subspace of an algebraic space `F` is an algebraic space `X` equipped with an
open immersion `ι : X ⟶ F`. -/
structure OpenSubspace {S : Scheme.{u}} (F : AlgebraicSpace S) where
  /-- The algebraic space underlying the open subspace. -/
  X : AlgebraicSpace S
  /-- The inclusion of the open subspace. -/
  ι : X ⟶ F
  /-- The inclusion is an open immersion of algebraic spaces. -/
  isOpenImmersion : IsOpenImmersion ι

namespace OpenSubspace

/-- The open subspace of `F` determined by an open immersion `ι : F' ⟶ F`. -/
def ofι {S : Scheme.{u}} {F F' : AlgebraicSpace S} (ι : F' ⟶ F) [h : IsOpenImmersion ι] :
    OpenSubspace F where
  X := F'
  ι := ι
  isOpenImmersion := h

/-- The inclusion of an open subspace is an open immersion, hence a monomorphism,
corresponding to the subfunctor reading `X ⊂ F`. -/
theorem spec {S : Scheme.{u}} {F : AlgebraicSpace S} (U : OpenSubspace F) :
    IsOpenImmersion U.ι ∧ Mono U.ι := sorry

/-- The identity open subspace `F ⊂ F`. -/
def id {S : Scheme.{u}} (F : AlgebraicSpace S) : OpenSubspace F :=
  ofι (𝟙 F)

end OpenSubspace

/-- A closed subspace of an algebraic space `F` is an algebraic space `X` equipped with a
closed immersion `ι : X ⟶ F`. -/
structure ClosedSubspace {S : Scheme.{u}} (F : AlgebraicSpace S) where
  /-- The algebraic space underlying the closed subspace. -/
  X : AlgebraicSpace S
  /-- The inclusion of the closed subspace. -/
  ι : X ⟶ F
  /-- The inclusion is a closed immersion of algebraic spaces. -/
  isClosedImmersion : IsClosedImmersion ι

namespace ClosedSubspace

/-- The closed subspace of `F` determined by a closed immersion `ι : F' ⟶ F`. -/
def ofι {S : Scheme.{u}} {F F' : AlgebraicSpace S} (ι : F' ⟶ F) [h : IsClosedImmersion ι] :
    ClosedSubspace F where
  X := F'
  ι := ι
  isClosedImmersion := h

/-- The inclusion of a closed subspace is a closed immersion, hence a monomorphism,
corresponding to the subfunctor reading `X ⊂ F`. -/
theorem spec {S : Scheme.{u}} {F : AlgebraicSpace S} (Z : ClosedSubspace F) :
    IsClosedImmersion Z.ι ∧ Mono Z.ι := sorry

/-- The identity closed subspace `F ⊂ F`. -/
def id {S : Scheme.{u}} (F : AlgebraicSpace S) : ClosedSubspace F :=
  ofι (𝟙 F)

end ClosedSubspace

/-- A locally closed subspace of an algebraic space `F` is an algebraic space `X` equipped
with an immersion `ι : X ⟶ F`. -/
structure LocallyClosedSubspace {S : Scheme.{u}} (F : AlgebraicSpace S) where
  /-- The algebraic space underlying the locally closed subspace. -/
  X : AlgebraicSpace S
  /-- The inclusion of the locally closed subspace. -/
  ι : X ⟶ F
  /-- The inclusion is an immersion of algebraic spaces. -/
  isImmersion : IsImmersion ι

namespace LocallyClosedSubspace

/-- The locally closed subspace of `F` determined by an immersion `ι : F' ⟶ F`. -/
def ofι {S : Scheme.{u}} {F F' : AlgebraicSpace S} (ι : F' ⟶ F) [h : IsImmersion ι] :
    LocallyClosedSubspace F where
  X := F'
  ι := ι
  isImmersion := h

/-- The inclusion of a locally closed subspace is an immersion, hence a monomorphism,
corresponding to the subfunctor reading `X ⊂ F`. -/
theorem spec {S : Scheme.{u}} {F : AlgebraicSpace S} (W : LocallyClosedSubspace F) :
    IsImmersion W.ι ∧ Mono W.ι := sorry

/-- The identity locally closed subspace `F ⊂ F`. -/
def id {S : Scheme.{u}} (F : AlgebraicSpace S) : LocallyClosedSubspace F :=
  ofι (𝟙 F)

end LocallyClosedSubspace

end AlgebraicGeometry.AlgebraicSpace
