/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.TopCat.DiagramOpens.Cohomology

/-!
# Component and Zariski cohomology of a simplicial space

Typed checks of cohomology on the diagram-open site and on its components.
-/

@[expose] public section

open CategoryTheory Opposite TopCat
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject

variable (X : SimplicialObject TopCat.{u})

#check (CategoryTheory.SimplicialObject.componentCohomologyFunctor X :
    ∀ (p q : ℕ)
    [HasSheafify (Opens.grothendieckTopology (X.obj (op ⦋p⦌))) AddCommGrpCat.{u}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology (X.obj (op ⦋p⦌))) AddCommGrpCat.{u})],
    Sheaf (zariskiTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{v})

#check (CategoryTheory.SimplicialObject.componentCohomology X :
    ∀ (F : Sheaf (zariskiTopology X) AddCommGrpCat.{u})
    (p q : ℕ)
    [HasSheafify (Opens.grothendieckTopology (X.obj (op ⦋p⦌))) AddCommGrpCat.{u}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology (X.obj (op ⦋p⦌))) AddCommGrpCat.{u})],
    AddCommGrpCat.{v})

#check (CategoryTheory.SimplicialObject.zariskiCohomologyFunctor X :
    ∀ (n : ℕ)
    [HasSheafify (zariskiTopology X) AddCommGrpCat.{u}]
    [HasExt.{v} (Sheaf (zariskiTopology X) AddCommGrpCat.{u})],
    Sheaf (zariskiTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{v})

#check (CategoryTheory.SimplicialObject.zariskiCohomology X :
    ∀ (F : Sheaf (zariskiTopology X) AddCommGrpCat.{u})
    [HasSheafify (zariskiTopology X) AddCommGrpCat.{u}]
    [HasExt.{v} (Sheaf (zariskiTopology X) AddCommGrpCat.{u})]
    (n : ℕ), AddCommGrpCat.{v})

#check (CategoryTheory.SimplicialObject.componentCohomologyFunctor_obj X :
    ∀ (F : Sheaf (zariskiTopology X) AddCommGrpCat.{u})
    (p q : ℕ)
    [HasSheafify (Opens.grothendieckTopology (X.obj (op ⦋p⦌))) AddCommGrpCat.{u}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology (X.obj (op ⦋p⦌))) AddCommGrpCat.{u})],
    (componentCohomologyFunctor X p q).obj F =
      (Sheaf.functorH (Opens.grothendieckTopology (X.obj (op ⦋p⦌))) q).obj
        ((sheafComponent X p AddCommGrpCat.{u}).obj F))

#check (CategoryTheory.SimplicialObject.zariskiCohomologyFunctor_obj X :
    ∀ (F : Sheaf (zariskiTopology X) AddCommGrpCat.{u})
    (n : ℕ)
    [HasSheafify (zariskiTopology X) AddCommGrpCat.{u}]
    [HasExt.{v} (Sheaf (zariskiTopology X) AddCommGrpCat.{u})],
    (zariskiCohomologyFunctor X n).obj F =
      (Sheaf.functorH (zariskiTopology X) n).obj F)

#check (CategoryTheory.SimplicialObject.componentCohomologyFunctor_map X :
    ∀
    {F G : Sheaf (zariskiTopology X) AddCommGrpCat.{u}} (α : F ⟶ G) (p q : ℕ)
    [HasSheafify (Opens.grothendieckTopology (X.obj (op ⦋p⦌))) AddCommGrpCat.{u}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology (X.obj (op ⦋p⦌))) AddCommGrpCat.{u})],
    (componentCohomologyFunctor X p q).map α =
      (Sheaf.functorH (Opens.grothendieckTopology (X.obj (op ⦋p⦌))) q).map
        ((sheafComponent X p AddCommGrpCat.{u}).map α))

end CategoryTheory.SimplicialObject
