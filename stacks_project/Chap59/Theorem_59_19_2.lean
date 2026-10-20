/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.SpectralSequence
import StacksCheckRecall

universe w z v u

/- Theorem 59.19.2 (Tag 03OW): a covering family of a site and an abelian sheaf admit a
Cech-to-cohomology spectral sequence whose second page is Cech cohomology of the cohomology
presheaf and whose abutment is site cohomology over the covered object. -/

@[stacks 03OW]
#check (CategoryTheory.Cech.spectralSequenceSystem_nonempty :
  ∀ {C : Type u} [CategoryTheory.Category.{v, u} C]
    {J : CategoryTheory.GrothendieckTopology C} {U : C} {ι : Type w}
    [CategoryTheory.Limits.HasFiniteProducts (CategoryTheory.Over U)]
    (family : ι → CategoryTheory.Over U)
    [CategoryTheory.Limits.HasProducts.{w} AddCommGrpCat.{z}]
    [CategoryTheory.HasSheafify J AddCommGrpCat.{v}]
    [CategoryTheory.HasExt.{z} (CategoryTheory.Sheaf J AddCommGrpCat.{v})],
    (J.over U).CoversTop family →
      Nonempty (CategoryTheory.Cech.SpectralSequenceSystem J U family))
