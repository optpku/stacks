/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.DerivedComparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u z

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] [UnivLE.{u + 1, z}]

/- 104.3.2.1 (1) The canonical smooth module comparison. -/
@[stacks 07AX] #check (AlgebraicGeometry.AlgebraicStack.lisseEtaleDerivedLowerShriekComparison :
  ∀ (φ : X ⟶ Y) [h_smooth : AlgebraicStack.Smooth φ]
    (G : RingedSite.Hom.ModuleDerived.{z}
      (RingedSite.ofRingSheaf (lisseEtaleTopology Y)
        (lisseEtaleInverseImageRingSheaf Y))),
    (lisseEtaleInclusionDerivedLowerShriek X).obj
      ((lisseEtaleDerivedInverseImage φ).obj G) ⟶
      (etaleDerivedInverseImage φ).obj
        ((lisseEtaleInclusionDerivedLowerShriek Y).obj G))

/- 104.3.2.1 (2) The canonical flat module comparison. -/
@[stacks 07AX] #check (AlgebraicGeometry.AlgebraicStack.flatFppfDerivedLowerShriekComparison :
  ∀ (φ : X ⟶ Y) [h_flat : AlgebraicStack.Flat φ]
    (G : RingedSite.Hom.ModuleDerived.{z}
      (RingedSite.ofRingSheaf (flatFppfTopology Y)
        (flatFppfInverseImageRingSheaf Y))),
    (flatFppfInclusionDerivedLowerShriek X).obj
      ((flatFppfDerivedInverseImage φ).obj G) ⟶
      (fppfDerivedInverseImage φ).obj
        ((flatFppfInclusionDerivedLowerShriek Y).obj G))

/- 104.3.2.1 (3) The canonical smooth abelian-sheaf comparison. -/
@[stacks 07AX] #check (AlgebraicGeometry.AlgebraicStack.lisseEtaleAbelianDerivedLowerShriekComparison :
  ∀ (φ : X ⟶ Y)
    [h_smooth : AlgebraicStack.Smooth φ]
    (G : DerivedCategory (Sheaf (lisseEtaleTopology Y) AddCommGrpCat.{z})),
    (lisseEtaleAbelianLowerShriekDerived X).obj
      ((lisseEtaleAbelianDerivedInverseImage φ).obj G) ⟶
      (etaleAbelianDerivedInverseImage φ).obj
        ((lisseEtaleAbelianLowerShriekDerived Y).obj G))

/- 104.3.2.1 (4) The canonical flat abelian-sheaf comparison. -/
@[stacks 07AX] #check (AlgebraicGeometry.AlgebraicStack.flatFppfAbelianDerivedLowerShriekComparison :
  ∀ (φ : X ⟶ Y) [h_flat : AlgebraicStack.Flat φ]
    (G : DerivedCategory (Sheaf (flatFppfTopology Y) AddCommGrpCat.{z})),
    (flatFppfAbelianLowerShriekDerived X).obj
      ((flatFppfAbelianDerivedInverseImage φ).obj G) ⟶
      (fppfAbelianDerivedInverseImage φ).obj
        ((flatFppfAbelianLowerShriekDerived Y).obj G))

