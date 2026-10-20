/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.CategoryTheory.Sites.Cech.Cofinal.Finite
public import ReasLib.CategoryTheory.Sites.Cofiltered.StageFamily.Colimit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of cofiltered stage families

This leaf owns the fixed-object cohomology diagrams attached to a compatible family on a
cofiltered site diagram.  The coefficient universe is pinned to the common site universe because
Mathlib's representable `cohomologyPresheafFunctor` uses the site's morphism universe; the output
Ext universe remains polymorphic.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CofilteredSiteDiagram
open CategoryTheory.Sheaf

noncomputable section

universe z u

namespace CategoryTheory.CofilteredSiteDiagram.StageFamily.Cohomology

variable (S : CofilteredSiteDiagram.{u, u, u})

section Comparison

variable [∀ i : S.I, HasWeakSheafify (S.stageTopology i) AddCommGrpCat.{u}]
variable [∀ i : S.I, HasSheafify (S.stageTopology i) AddCommGrpCat.{u}]
variable [∀ i : S.I, HasExt.{z} (Sheaf (S.stageTopology i) AddCommGrpCat.{u})]
variable [HasWeakSheafify S.colimitTopology AddCommGrpCat.{u}]
variable [HasSheafify S.colimitTopology AddCommGrpCat.{u}]
variable [HasExt.{z} (Sheaf S.colimitTopology AddCommGrpCat.{u})]
variable [∀ {i j : S.I} (a : j ⟶ i),
  ∀ G : (S.stage i)ᵒᵖ ⥤ AddCommGrpCat.{u},
    (S.stageFunctor a).op.HasLeftKanExtension G]
variable [∀ i : S.I,
  ∀ G : (S.stage i)ᵒᵖ ⥤ AddCommGrpCat.{u},
    (S.stageCoconeFunctor i).op.HasLeftKanExtension G]
variable [HasColimitsOfShape S.Iᵒᵖ (Sheaf S.colimitTopology AddCommGrpCat.{u})]

/-- The cohomology functor at the image of a stage object in the colimit site. -/
@[stacks 09YP "fixed-object cohomology functor"]
abbrev objectCohomology (p : ℕ) {i : S.I} (X : S.stage i) :
    Sheaf S.colimitTopology AddCommGrpCat.{u} ⥤ AddCommGrpCat.{z} :=
  Sheaf.cohomologyPresheafFunctor.{z, u, u} S.colimitTopology p ⋙
    (evaluation _ AddCommGrpCat.{z}).obj
      (op ((S.stageCoconeFunctor i).obj X))

/-- The ambient `S.Iᵒᵖ`-diagram of fixed-object cohomology for a compatible stage family. -/
@[stacks 09YP "fixed-object cohomology diagram"]
abbrev diagram
    (F : StageFamily S AddCommGrpCat.{u}) (p : ℕ) {i : S.I} (X : S.stage i) :
    S.Iᵒᵖ ⥤ AddCommGrpCat.{z} :=
  CofilteredSiteDiagram.StageFamily.diagram F ⋙ objectCohomology S p X

/-- The source diagram over `(Over i)ᵒᵖ`, obtained by restricting the ambient diagram. -/
@[stacks 09YP "over-category cohomology diagram"]
abbrev over
    (F : StageFamily S AddCommGrpCat.{u}) (p : ℕ) {i : S.I} (X : S.stage i) :
    (Over i)ᵒᵖ ⥤ AddCommGrpCat.{z} :=
  (Over.forget i).op ⋙ diagram S F p X

/-- The restricted diagram identifies objectwise with the source-text terms `H^p(u_a(X), 𝓕_j)`. -/
@[stacks 09YP "objectwise cohomology comparison"]
theorem over_obj_iso
    (F : StageFamily S AddCommGrpCat.{u}) (p : ℕ) {i : S.I} (X : S.stage i)
    (A : (Over i)ᵒᵖ) :
    IsIsomorphic
      ((over S F p X).obj A)
      ((F.obj A.unop.left).H' p (S.overImage X A)) := sorry

/-- The canonical comparison from the restricted over-category colimit to colimit-site
cohomology. -/
@[stacks 09YP "cohomology colimit comparison"]
noncomputable def comparison
    (F : StageFamily S AddCommGrpCat.{u}) (p : ℕ) {i : S.I} (X : S.stage i)
    [HasColimit (over S F p X)] [HasColimit (diagram S F p X)] :
    colimit (over S F p X) ⟶
      F.colimitSheaf.H' p ((S.stageCoconeFunctor i).obj X) :=
  (Functor.Final.colimitIso ((Over.forget i).op) (diagram S F p X)).hom ≫
    colimit.post (CofilteredSiteDiagram.StageFamily.diagram F) (objectCohomology S p X)

/-- The canonical over-category cohomology comparison is an isomorphism. -/
@[stacks 09YP "cohomology colimit comparison isomorphism"]
theorem comparison_isIso
    (F : StageFamily S AddCommGrpCat.{u}) (p : ℕ) {i : S.I} (X : S.stage i)
    [HasColimit (over S F p X)] [HasColimit (diagram S F p X)] :
    IsIso
      ((comparison S F p X) :
        colimit (over S F p X) ⟶
          F.colimitSheaf.H' p ((S.stageCoconeFunctor i).obj X)) := sorry

/-- Lemma 21.16.6 (09YP): the over-category colimit of fixed-object cohomology is
isomorphic to the cohomology of the colimit sheaf. -/
@[stacks 09YP]
theorem colimit_isomorphic
    (F : StageFamily S AddCommGrpCat.{u}) (p : ℕ) {i : S.I} (X : S.stage i)
    [HasColimit (over S F p X)] [HasColimit (diagram S F p X)] :
    IsIsomorphic
      (colimit (over S F p X))
      (F.colimitSheaf.H' p ((S.stageCoconeFunctor i).obj X)) := sorry

end Comparison

end CategoryTheory.CofilteredSiteDiagram.StageFamily.Cohomology

end
