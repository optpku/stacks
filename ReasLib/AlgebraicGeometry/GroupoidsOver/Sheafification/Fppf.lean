/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Sheafification.Sites

/-!
# Sheafification on the inherited fppf site

Abelian-group sheaves on the inherited fppf site admit weak sheafification,
and sheafification equivalences are locally bijective morphisms.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} (X : GroupoidsOver S)

/-- Weak sheafification of abelian groups exists on the inherited fppf topology of
a category fibred in groupoids. -/
instance inheritedFppfTopology_hasWeakSheafify :
    HasWeakSheafify (inheritedFppfTopology X) AddCommGrpCat.{u} :=
  Sheafification.stackHasWeakSheafify X

/-- On the inherited fppf topology of a category fibred in groupoids, sheafification
equivalences are the locally bijective morphisms. -/
instance inheritedFppfTopology_wEqualsLocallyBijective :
    (inheritedFppfTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

end AlgebraicGeometry.GroupoidsOver
