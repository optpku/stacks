/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.SheafHom
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeHom

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B) (T : AlgebraicSpace S)

/- Lemma 97.10.1 (1): `Mor_B(Z, X)` is a sheaf on `(Sch/S)_fppf`. -/
@[stacks 05Y3]
#check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.isSheaf Z.hom X.hom :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (AlgebraicGeometry.AlgebraicSpace.RelativeHom.presheaf Z.hom X.hom))

/- Lemma 97.10.1 (2): for an algebraic space `T` over `S`, sheaf morphisms
`T ⟶ Mor_B(Z, X)` correspond canonically to pairs `(a, b)` as in (05Y1). -/
@[stacks 05Y3]
#check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.homEquiv Z X T :
    (AlgebraicGeometry.AlgebraicSpace.toSheaf.obj T ⟶
      AlgebraicGeometry.AlgebraicSpace.RelativeHom.sheaf Z.hom X.hom) ≃
      AlgebraicGeometry.AlgebraicSpace.RelativeHom.SpacePair Z X T)
