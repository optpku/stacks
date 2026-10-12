/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import stacks_project.Chap85.Lemma_85_2_5

/-!
# Component and Zariski cohomology of a simplicial space

Functorial cohomology of an abelian sheaf on the Zariski site of a simplicial
topological space, and of its degree-`p` components.
-/

@[expose] public section

open CategoryTheory Opposite TopCat
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject

variable (X : SimplicialObject TopCat.{u})

/-- The functor sending an abelian sheaf `F` on `X_Zar` to the cohomology
`H^q(X_p, F_p)` of its degree-`p` component. -/
def componentCohomologyFunctor (p q : ℕ)
    [HasSheafify (Opens.grothendieckTopology (X.obj (op ⦋p⦌))) AddCommGrpCat.{u}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology (X.obj (op ⦋p⦌))) AddCommGrpCat.{u})] :
    Sheaf (zariskiTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{v} :=
  sheafComponent X p AddCommGrpCat.{u} ⋙
    Sheaf.functorH (Opens.grothendieckTopology (X.obj (op ⦋p⦌))) q

/-- The cohomology group `H^q(X_p, F_p)` of the degree-`p` component of an abelian
sheaf on `X_Zar`. -/
abbrev componentCohomology (F : Sheaf (zariskiTopology X) AddCommGrpCat.{u})
    (p q : ℕ)
    [HasSheafify (Opens.grothendieckTopology (X.obj (op ⦋p⦌))) AddCommGrpCat.{u}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology (X.obj (op ⦋p⦌))) AddCommGrpCat.{u})] :
    AddCommGrpCat.{v} :=
  (componentCohomologyFunctor X p q).obj F

/-- The functor sending an abelian sheaf `F` on `X_Zar` to the cohomology
`H^n(X_Zar, F)`. -/
def zariskiCohomologyFunctor (n : ℕ)
    [HasSheafify (zariskiTopology X) AddCommGrpCat.{u}]
    [HasExt.{v} (Sheaf (zariskiTopology X) AddCommGrpCat.{u})] :
    Sheaf (zariskiTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{v} :=
  Sheaf.functorH (zariskiTopology X) n

/-- The cohomology group `H^n(X_Zar, F)` of an abelian sheaf on the Zariski site of
a simplicial topological space. -/
abbrev zariskiCohomology (F : Sheaf (zariskiTopology X) AddCommGrpCat.{u})
    [HasSheafify (zariskiTopology X) AddCommGrpCat.{u}]
    [HasExt.{v} (Sheaf (zariskiTopology X) AddCommGrpCat.{u})]
    (n : ℕ) : AddCommGrpCat.{v} :=
  (zariskiCohomologyFunctor X n).obj F

/-- Evaluating the component cohomology functor is cohomology of the degree-`p`
component sheaf. -/
theorem componentCohomologyFunctor_obj (F : Sheaf (zariskiTopology X) AddCommGrpCat.{u})
    (p q : ℕ)
    [HasSheafify (Opens.grothendieckTopology (X.obj (op ⦋p⦌))) AddCommGrpCat.{u}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology (X.obj (op ⦋p⦌))) AddCommGrpCat.{u})] :
    (componentCohomologyFunctor X p q).obj F =
      (Sheaf.functorH (Opens.grothendieckTopology (X.obj (op ⦋p⦌))) q).obj
        ((sheafComponent X p AddCommGrpCat.{u}).obj F) :=
  sorry

/-- Evaluating the Zariski cohomology functor is `Sheaf.functorH` on `X_Zar`. -/
theorem zariskiCohomologyFunctor_obj (F : Sheaf (zariskiTopology X) AddCommGrpCat.{u})
    (n : ℕ)
    [HasSheafify (zariskiTopology X) AddCommGrpCat.{u}]
    [HasExt.{v} (Sheaf (zariskiTopology X) AddCommGrpCat.{u})] :
    (zariskiCohomologyFunctor X n).obj F =
      (Sheaf.functorH (zariskiTopology X) n).obj F :=
  sorry

/-- The component cohomology functor acts on morphisms by the cohomology of the
degree-`p` component map. -/
theorem componentCohomologyFunctor_map
    {F G : Sheaf (zariskiTopology X) AddCommGrpCat.{u}} (α : F ⟶ G) (p q : ℕ)
    [HasSheafify (Opens.grothendieckTopology (X.obj (op ⦋p⦌))) AddCommGrpCat.{u}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology (X.obj (op ⦋p⦌))) AddCommGrpCat.{u})] :
    (componentCohomologyFunctor X p q).map α =
      (Sheaf.functorH (Opens.grothendieckTopology (X.obj (op ⦋p⦌))) q).map
        ((sheafComponent X p AddCommGrpCat.{u}).map α) :=
  sorry

end CategoryTheory.SimplicialObject
