/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Regular.Etale

/-!
# Regular algebraic spaces

An algebraic space is regular when it admits a representable étale locally-surjective atlas
from a regular scheme, in the sense of the étale-local type-property of schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is regular if it admits a representable étale locally-surjective atlas
whose source is a regular scheme. -/
@[mk_iff]
class IsRegular {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- There is a representable étale locally-surjective atlas from a regular scheme. -/
  exists_regular_etaleCover :
    existsSurjectiveEtale (Scheme.Regular : ObjectProperty Scheme.{u}) X

namespace IsRegular

/-- A regular algebraic space admits a representable étale locally-surjective atlas from a
regular scheme. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [IsRegular X] :
    existsSurjectiveEtale (Scheme.Regular : ObjectProperty Scheme.{u}) X :=
  sorry

/-- A representable étale locally-surjective atlas from a regular scheme witnesses that the
algebraic space is regular. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : existsSurjectiveEtale (Scheme.Regular : ObjectProperty Scheme.{u}) X) :
    IsRegular X :=
  sorry

/-- A regular algebraic space is normal. -/
instance instIsNormal {S : Scheme.{u}} (X : AlgebraicSpace S) [IsRegular X] :
    IsNormal X :=
  sorry

end IsRegular

/-- A regular scheme over `S`, viewed as an algebraic space, is regular. -/
instance instIsRegular_ofOver {S : Scheme.{u}} (T : Over S) [Scheme.Regular T.left] :
    IsRegular (ofOver T) where
  exists_regular_etaleCover :=
    (existsSurjectiveEtale_ofOver (Scheme.Regular : ObjectProperty Scheme.{u}) T).mpr
      inferInstance

/-- An algebraic space is regular if and only if every étale morphism from a scheme to it has
regular source. -/
theorem isRegular_iff_forallEtale {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsRegular X ↔ forallEtale (Scheme.Regular : ObjectProperty Scheme.{u}) X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
