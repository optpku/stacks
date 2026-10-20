/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.PreRelation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf

/-!
# Representable quotient sheaves of pre-relations on algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- A pre-relation has a quotient representable by an algebraic space when its quotient sheaf is
isomorphic to the sheaf of points of an algebraic space over the base scheme. -/
abbrev HasAlgebraicSpaceQuotient {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) : Prop :=
  ∃ M : AlgebraicSpace S, Nonempty (toSheaf.obj M ≅ P.quotientSheaf)

/-- A pre-relation has a representable quotient when its quotient sheaf is representable by a
scheme over the base scheme. -/
abbrev HasRepresentableQuotient {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) : Prop :=
  (P.quotientSheaf).obj.IsRepresentable

/-- A representable quotient is equivalent to the quotient sheaf being the sheaf of points of an
explicit scheme over the base. -/
theorem hasRepresentableQuotient_iff_exists_ofOver {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U : Over B} (P : PreRelation U) :
    HasRepresentableQuotient P ↔
      ∃ T : Over S, Nonempty (toSheaf.obj (ofOver T) ≅ P.quotientSheaf) :=
  sorry

/-- A quotient representable by a scheme is representable by an algebraic space. -/
theorem hasAlgebraicSpaceQuotient_of_hasRepresentableQuotient {S : Scheme.{u}}
    {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
    (h : HasRepresentableQuotient P) : HasAlgebraicSpaceQuotient P :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- A groupoid in algebraic spaces has a quotient representable by an algebraic space when the
quotient of its underlying pre-relation is representable by an algebraic space. -/
abbrev HasAlgebraicSpaceQuotient {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) : Prop :=
  G.toPreRelation.HasAlgebraicSpaceQuotient

/-- A groupoid in algebraic spaces has a representable quotient when the quotient of its
underlying pre-relation is representable by a scheme. -/
abbrev HasRepresentableQuotient {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) : Prop :=
  G.toPreRelation.HasRepresentableQuotient

end AlgebraicGeometry.GroupoidAlgebraicSpace
