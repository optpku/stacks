/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars.Hom
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} {X Z B T : AlgebraicSpace S} (f : X ⟶ Z) (g : Z ⟶ B)

/- Lemma 97.11.1 (1): `Res_{Z/B}(X)` is a sheaf on `(Sch/S)_fppf`. -/
@[stacks 05YB]
#check (AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars.isSheaf f g :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (restrictionOfScalars f g))

/- Lemma 97.11.1 (2): for an algebraic space `T` over `S`, sheaf morphisms
`T ⟶ Res_{Z/B}(X)` correspond canonically to pairs `(a, b)` as in (05Y9). -/
@[stacks 05YB]
#check (AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars.homEquiv f g :
    (toSheaf.obj T ⟶ RestrictionOfScalars.sheaf f g) ≃ RestrictScalars.Pair f g T)
