/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Injective
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y Z : Scheme.{u}}
variable [∀ W : Scheme.{u}, HasSheafify W.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ W : Scheme.{u},
    HasInjectiveResolutions (Sheaf W.smallEtaleTopology AddCommGrpCat.{u})]

/-- For proper morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` with `f` surjective,
commutation of torsion étale cohomology with base change for `f` and `f ≫ g`
implies commutation with base change for `g`. -/
theorem cohomologyCommutesWithBaseChange_of_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f] [IsProper g] [Surjective f]
    (hf : CohomologyCommutesWithBaseChange f)
    (hgf : CohomologyCommutesWithBaseChange (f ≫ g)) :
    CohomologyCommutesWithBaseChange g := sorry

end AlgebraicGeometry.Scheme.Hom

end
