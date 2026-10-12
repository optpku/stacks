/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer
public import ReasLib.Topology.Sheaf.GlobalSections
public import ReasLib.Topology.Opens.Instances
public import Mathlib.Topology.Sheaves.AddCommGrpCat

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

variable (Y : TopCat.{u})
variable [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]

/-- The top open of a topological space is terminal in its opens category. -/
def topOpenIsTerminal : IsTerminal (⊤ : Opens Y) :=
  Preorder.isTerminalTop (Opens Y)

/-- The constant sheaf of integers on a topological space. -/
abbrev constantIntegerSheaf : Y.Sheaf AddCommGrpCat.{u} :=
  CategoryTheory.constantIntegerSheaf (Opens.grothendieckTopology Y)

/-- Morphisms from the constant integer sheaf are equivalent to sections on the top open. -/
noncomputable def constantIntegerHomEquivTopSection
    (G : Y.Sheaf AddCommGrpCat.{u}) :
    (constantIntegerSheaf Y ⟶ G) ≃ G.obj.obj (Opposite.op (⊤ : Opens Y)) :=
  (CategoryTheory.Sheaf.globalSectionsEquivConstantIntegerSheafHomOnSite
      (Opens.grothendieckTopology Y) G).symm.trans
    (CategoryTheory.Iso.addCommGroupIsoToAddEquiv
      ((CategoryTheory.Sheaf.ΓNatIsoSheafSections
        (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
        (topOpenIsTerminal Y)).app G)).toEquiv

/-- The top-section equivalence is natural in the target sheaf. -/
theorem constantIntegerHomEquivTopSection_naturality
    {G H : Y.Sheaf AddCommGrpCat.{u}} (f : G ⟶ H)
    (φ : constantIntegerSheaf Y ⟶ G) :
    constantIntegerHomEquivTopSection Y H (φ ≫ f) =
      ((f.hom.app (Opposite.op (⊤ : Opens Y))).hom
        (constantIntegerHomEquivTopSection Y G φ)) := sorry

end TopCat.Sheaf
