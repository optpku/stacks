/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Invariant

universe u

open CategoryTheory

variable {S : AlgebraicGeometry.Scheme.{u}} {U : Over S}

#check (AlgebraicGeometry.Scheme.PreRelation.IsSetInvariant :
  AlgebraicGeometry.Scheme.PreRelation U → Set U.left → Prop)

#check (AlgebraicGeometry.Scheme.PreRelation.IsOpenInvariant :
  AlgebraicGeometry.Scheme.PreRelation U → U.left.Opens → Prop)

#check (AlgebraicGeometry.Scheme.PreRelation.IsClosedInvariant :
  AlgebraicGeometry.Scheme.PreRelation U → U.left.IdealSheafData → Prop)

#check (AlgebraicGeometry.Scheme.PreRelation.IsInvariant :
  AlgebraicGeometry.Scheme.PreRelation U → Subobject U.left → Prop)
