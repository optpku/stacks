/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Category.TopCat.DiagramOpens.Site

@[expose] public section

open CategoryTheory TopologicalSpace TopCat

universe u v w

namespace TopCat.DiagramOpens

variable {C : Type u} [Category.{v} C] (F : C ⥤ TopCat.{w})

#check (precoverage F : Precoverage (DiagramOpens F))
#check (coverings F : ∀ U : DiagramOpens F, Set (PreZeroHypercover U))
#check (topology F : GrothendieckTopology (DiagramOpens F))
#check (@ofArrows_mem_precoverage_iff C _ F)

end TopCat.DiagramOpens

namespace CategoryTheory.SimplicialObject

#check (zariskiSite : ∀ {u}, SimplicialObject TopCat.{u} → Type _)
#check (zariskiPrecoverage : ∀ {u}, (X : SimplicialObject TopCat.{u}) →
  Precoverage (zariskiSite X))
#check (zariskiCoverings : ∀ {u},
  (X : SimplicialObject TopCat.{u}) →
    ∀ U : zariskiSite X, Set (PreZeroHypercover U))
#check (zariskiTopology : ∀ {u}, (X : SimplicialObject TopCat.{u}) →
  GrothendieckTopology (zariskiSite X))
#check (instZariskiCoveringsIsSite : ∀ {u} (X : SimplicialObject TopCat.{u}),
  PreZeroHypercover.IsSite (zariskiCoverings X))

end CategoryTheory.SimplicialObject
