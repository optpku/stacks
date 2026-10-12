/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Over
public import stacks_project.Chap73.Definition_73_8_5_Site

/-!
# Localized big ph sites of algebraic spaces

The big ph site `(Spaces / X)_ph` is the Sites 7.25 localization of
`(Spaces / S)_ph` at an algebraic space `X` over `S`. After generating
the Grothendieck topology, every chosen cardinal truncation from
Definition 73.8.5 induces the same slice topology `overPhTopology X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The localized big ph topology on `Over X`, i.e. `(Spaces / X)_ph`. -/
abbrev overPhTopology {S : Scheme.{u}} (X : AlgebraicSpace S) :
    GrothendieckTopology (Over X) :=
  (phPrecoverage : Precoverage (AlgebraicSpace S)).toGrothendieck.over X

/-- `overPhTopology X` is the localization of the ph Grothendieck topology at
`X`. -/
theorem overPhTopology_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    overPhTopology X =
      (phPrecoverage : Precoverage (AlgebraicSpace S)).toGrothendieck.over X :=
  sorry

/-- A sieve on `Over X` covers for `overPhTopology` if and only if its image
under `Sieve.overEquiv` covers in `(Spaces / S)_ph`. -/
theorem mem_overPhTopology_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {Y : Over X} (R : Sieve Y) :
    R ∈ overPhTopology X Y ↔
      Sieve.overEquiv Y R ∈
        (phPrecoverage : Precoverage (AlgebraicSpace S)).toGrothendieck Y.left :=
  sorry

/-- Localization of a chosen big ph site at `X` agrees with
`overPhTopology X`. -/
theorem ChosenBigPhSite.over_eq {S : Scheme.{u}} (J : ChosenBigPhSite S)
    (X : AlgebraicSpace S) :
    J.toGrothendieck.over X = overPhTopology X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
