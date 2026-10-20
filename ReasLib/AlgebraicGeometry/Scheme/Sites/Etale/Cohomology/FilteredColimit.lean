/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Pullback
public import ReasLib.CategoryTheory.Sites.Cohomology.Map

/-!
# Filtered colimits of global étale cohomology

Global étale cohomology of abelian sheaves on a quasi-compact and quasi-separated
scheme commutes with directed colimits through the canonical comparison morphism.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X : Scheme.{u}}
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable {I : Type u} [Preorder I]
variable (F : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
variable (p : ℕ)

/-- The diagram of global degree-`p` étale cohomology groups of a diagram of
abelian sheaves on the small étale site of a fixed scheme. -/
def sheafCohomologyDiagram : I ⥤ AddCommGrpCat.{u} where
  obj i := (F.obj i).H' p (globalEtale X)
  map {i j} hij := Sheaf.cohomologyMap (F.map hij) p (globalEtale X)
  map_id := sorry
  map_comp := sorry

/-- Evaluating the cohomology diagram gives global étale cohomology of the stage sheaf. -/
theorem sheafCohomologyDiagram_obj (i : I) :
    (sheafCohomologyDiagram F p).obj i = (F.obj i).H' p (globalEtale X) := sorry

/-- The canonical comparison from the colimit of global degree-`p` étale cohomology
groups to global degree-`p` étale cohomology of the colimit sheaf. -/
def sheafCohomologyComparison [HasColimit F] [HasColimit (sheafCohomologyDiagram F p)] :
    colimit (sheafCohomologyDiagram F p) ⟶ (colimit F).H' p (globalEtale X) :=
  colimit.desc (sheafCohomologyDiagram F p)
    { pt := (colimit F).H' p (globalEtale X)
      ι :=
        { app := fun i => Sheaf.cohomologyMap (colimit.ι F i) p (globalEtale X)
          naturality := sorry } }

/-- Composing a cohomology colimit injection with the comparison gives the
cohomology map induced by the corresponding sheaf colimit injection. -/
theorem sheafCohomologyComparison_ι [HasColimit F] [HasColimit (sheafCohomologyDiagram F p)]
    (i : I) :
    colimit.ι (sheafCohomologyDiagram F p) i ≫ sheafCohomologyComparison F p =
      Sheaf.cohomologyMap (colimit.ι F i) p (globalEtale X) := sorry

variable [CompactSpace X] [QuasiSeparatedSpace X]
variable [Nonempty I] [IsDirected I (· ≤ ·)]
variable [HasColimit F] [HasColimit (sheafCohomologyDiagram F p)]

/-- Global étale cohomology on a quasi-compact and quasi-separated scheme commutes
with directed colimits of abelian sheaves in every natural-number degree. -/
theorem etaleCohomology_colimit : IsIso (sheafCohomologyComparison F p) := sorry

end AlgebraicGeometry.Scheme.Etale

end
