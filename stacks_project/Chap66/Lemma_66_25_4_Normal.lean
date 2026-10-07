module

public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import stacks_project.Chap66.Lemma_66_7_1
public import stacks_project.Chap66.Remark_66_7_3_EtaleLocal

/-!
# Normal algebraic spaces

An algebraic space is normal when it admits a representable étale locally-surjective atlas
from a normal scheme, in the sense of the étale-local type-property of schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is normal if it admits a representable étale locally-surjective atlas
whose source is a normal scheme. -/
@[mk_iff]
class IsNormal {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- There is a representable étale locally-surjective atlas from a normal scheme. -/
  exists_normal_etaleCover :
    existsSurjectiveEtale (Scheme.isNormal : ObjectProperty Scheme.{u}) X

namespace IsNormal

/-- A normal algebraic space admits a representable étale locally-surjective atlas from a
normal scheme. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [IsNormal X] :
    existsSurjectiveEtale (Scheme.isNormal : ObjectProperty Scheme.{u}) X :=
  sorry

/-- A representable étale locally-surjective atlas from a normal scheme witnesses that the
algebraic space is normal. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : existsSurjectiveEtale (Scheme.isNormal : ObjectProperty Scheme.{u}) X) :
    IsNormal X :=
  sorry

/-- A normal scheme over `S`, viewed as an algebraic space, is normal. -/
theorem ofOver {S : Scheme.{u}} {T : Over S} (h : Scheme.isNormal T.left) :
    IsNormal (ofOver T) :=
  sorry

end IsNormal

/-- An algebraic space is normal if and only if every étale morphism from a scheme to it has
normal source. -/
theorem isNormal_iff_forallEtale {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsNormal X ↔ forallEtale (Scheme.isNormal : ObjectProperty Scheme.{u}) X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
