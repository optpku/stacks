/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Coherence

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [IsSeparated f] [LocallyOfFiniteType f]
variable [IsSeparated g] [LocallyOfFiniteType g]

#check (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekComp f g :
  etaleLowerShriek f ⋙ etaleLowerShriek g ⟶ etaleLowerShriek (f ≫ g))

#check (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekCompIso f g :
  etaleLowerShriek f ⋙ etaleLowerShriek g ≅ etaleLowerShriek (f ≫ g))
