/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap48.Remark_48_32_5_Flattening
import StacksCheckRecall

open CategoryTheory Opposite
open scoped CategoryTheory

universe u v

/- Remark 48.32.5: after choosing sequential presentations `M k` for the objects `Rg_! Mₖ`
and sequential representatives for their transition morphisms, `diagonalPro M r` models
`Rg_! Rf_! K`. Its realized Hom functor is naturally identified, componentwise bijectively,
with the iterated colimit of the stagewise Hom functors. This characterization determines its
pro-isomorphism class; functoriality in `K` is deferred to the next lemma.
-/
@[stacks 0G54] #check (CategoryTheory.Pro.SequentialHom.diagonalPro :
  ∀ {C : Type u} [Category.{v} C]
    (M : ℕ → ℕᵒᵖ ⥤ C)
    (_ : ∀ k, Pro.SequentialHom (M (k + 1)) (M k)), Pro C)

#check (CategoryTheory.Pro.SequentialHom.diagonalProHomComparison :
  ∀ {C : Type u} [Category.{v} C]
    (M : ℕ → ℕᵒᵖ ⥤ C)
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k)),
    ((Pro.inclusion C).obj
      (CategoryTheory.Pro.SequentialHom.diagonalPro M r)).unop ⟶
      CategoryTheory.Pro.SequentialHom.iteratedHomColimit M r)

#check (CategoryTheory.Pro.SequentialHom.diagonalProHomComparison_bijective :
  ∀ {C : Type u} [Category.{v} C]
    {M : ℕ → ℕᵒᵖ ⥤ C}
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k))
    (_ : ∀ k n, n ≤ (r k).reindex n) (N : C),
    Function.Bijective
      ((CategoryTheory.Pro.SequentialHom.diagonalProHomComparison M r).app N))

#check (CategoryTheory.Pro.SequentialHom.isoDiagonalPro :
  ∀ {C : Type u} [Category.{v} C]
    {M : ℕ → ℕᵒᵖ ⥤ C}
    (r : ∀ k, Pro.SequentialHom (M (k + 1)) (M k))
    (_ : ∀ k n, n ≤ (r k).reindex n) (P : Pro C)
    (comparison : ((Pro.inclusion C).obj P).unop ⟶
      CategoryTheory.Pro.SequentialHom.iteratedHomColimit M r)
    (_ : ∀ N, Function.Bijective (comparison.app N)),
    P ≅ CategoryTheory.Pro.SequentialHom.diagonalPro M r)
