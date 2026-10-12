/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Topology.Sheaves.Sheaf
public import ReasLib.Topology.Opens.Instances

/-!
# Compatibility facade for the constant integer sheaf on a topological space

The site-generic owner is `CategoryTheory.constantIntegerSheaf` together with
the APIs in `ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer`.  This file
retains the Chapter 20 names specialized to `Opens X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace

noncomputable section

universe u

section

local instance sheafPreadditive (Y : TopCat.{u}) : Preadditive (Y.Sheaf AddCommGrpCat.{u}) :=
  inferInstanceAs
    (Preadditive
      (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}))

/-- The top open is terminal in `Opens Y`. -/
def topOpenIsTerminal (Y : TopCat.{u}) : IsTerminal (⊤ : Opens Y) :=
  Preorder.isTerminalTop (Opens Y)

/-- The constant integer sheaf on `X`, retained under the historical topological-space name. -/
abbrev constantIntegerSheaf (X : TopCat.{u})
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] :
    X.Sheaf AddCommGrpCat.{u} :=
  CategoryTheory.constantIntegerSheaf (Opens.grothendieckTopology X)

/-- Additive maps from `ULift ℤ` are determined by the image of `1`.  The canonical owner is
`uliftZMultiplesHom`. -/
noncomputable abbrev uliftIntAddHomEquiv (A : Type u) [AddCommGroup A] :
    (ULift.{u} ℤ →+ A) ≃ A :=
  (uliftZMultiplesHom A).symm

/-- Morphisms from `AddCommGrpCat.of (ULift ℤ)` are determined by the image of `1`.  The
canonical additive refinement is `AddCommGrpCat.uliftZMultiplesAddEquiv`. -/
noncomputable abbrev uliftIntObjectHomEquiv (A : AddCommGrpCat.{u}) :
    (AddCommGrpCat.of (ULift.{u} ℤ) ⟶ A) ≃ A :=
  (AddCommGrpCat.uliftZMultiplesAddEquiv A).toEquiv

/-- Morphisms from the constant integer sheaf on a space `Y` are equivalent to sections over the
top open. -/
noncomputable def constantIntegerSheaf_hom_equiv_top_section
    (Y : TopCat.{u})
    [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
    (G : Y.Sheaf AddCommGrpCat.{u}) :
    (constantIntegerSheaf Y ⟶ G) ≃ G.obj.obj (Opposite.op (⊤ : Opens Y)) :=
  (CategoryTheory.Sheaf.globalSectionsEquivConstantIntegerSheafHomOnSite
      (Opens.grothendieckTopology Y) G).symm.trans
    (CategoryTheory.Iso.addCommGroupIsoToAddEquiv
      ((CategoryTheory.Sheaf.ΓNatIsoSheafSections
        (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}
        (topOpenIsTerminal Y)).app G)).toEquiv

/-- Morphisms from the constant integer sheaf on a space `Y` are additively equivalent to
sections over the top open. -/
noncomputable def constantIntegerSheaf_hom_addEquiv_top_section
    (Y : TopCat.{u})
    [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
    (G : Y.Sheaf AddCommGrpCat.{u}) :
    (constantIntegerSheaf Y ⟶ G) ≃+ G.obj.obj (Opposite.op (⊤ : Opens Y)) :=
  (CategoryTheory.Sheaf.globalSectionsAddEquivConstantIntegerSheafHomOnSite
      (Opens.grothendieckTopology Y) G).symm.trans
    (CategoryTheory.Iso.addCommGroupIsoToAddEquiv
      ((CategoryTheory.Sheaf.ΓNatIsoSheafSections
        (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}
        (topOpenIsTerminal Y)).app G))

namespace CategoryTheory.Sheaf

/-- Global sections of an additive sheaf on a topological space identify additively with
morphisms from the constant integer sheaf. -/
noncomputable def globalSectionsAddEquivConstantIntegerSheafHom
    (Y : TopCat.{u})
    [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
    (G : Y.Sheaf AddCommGrpCat.{u}) :
    ((Γ (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj G) ≃+
      (_root_.constantIntegerSheaf Y ⟶ G) :=
  globalSectionsAddEquivConstantIntegerSheafHomOnSite
    (Opens.grothendieckTopology Y) G

end CategoryTheory.Sheaf

end
