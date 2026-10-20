/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.AutEmbedding
public import ReasLib.CategoryTheory.Functor.AutTopology
public import Mathlib.CategoryTheory.Galois.Topology
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.PreGaloisCategory

universe u v w

/- Lemma 58.3.1: natural automorphisms form a closed subgroup of the product
of objectwise automorphism groups with pointwise topology; finite fibers give
a profinite group. -/
@[stacks 0BMR] #check
  (CategoryTheory.Functor.autEmbedding_isClosedEmbedding :
    ∀ {C : Type u} [Category.{v} C] (F : C ⥤ Type w),
      Topology.IsClosedEmbedding (CategoryTheory.Functor.autEmbedding F))

#check
  (CategoryTheory.Functor.autEmbedding_range_eq_compatibility :
    ∀ {C : Type u} [Category.{v} C] (F : C ⥤ Type w),
      Set.range (CategoryTheory.Functor.autEmbedding F) =
        ⋂ (f : CategoryTheory.Arrow C),
          {a | F.map f.hom ≫ (a f.right).hom =
            (a f.left).hom ≫ F.map f.hom})

#check
  (CategoryTheory.Functor.autEmbedding_range_separation :
    ∀ {C : Type u} [Category.{v} C] (F : C ⥤ Type w)
      (a : ∀ X : C, Aut (F.obj X)),
      a ∉ Set.range (CategoryTheory.Functor.autEmbedding F) →
        ∃ (f : CategoryTheory.Arrow C) (x : F.obj f.left),
          F.map f.hom ((a f.left).hom x) ≠
            (a f.right).hom (F.map f.hom x))

#check
  (CategoryTheory.PreGaloisCategory.autEmbedding_isClosedEmbedding :
    ∀ {C : Type u} [Category.{v} C] (F : C ⥤ FintypeCat.{w}),
      Topology.IsClosedEmbedding (CategoryTheory.PreGaloisCategory.autEmbedding F))

section FiniteFibers

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)
  [∀ object : C, Finite (F.obj object)]

#check (CategoryTheory.Functor.autCompactSpace F : CompactSpace (Aut F))

#check (ProfiniteGrp.of (Aut F) : ProfiniteGrp.{max u w})

end FiniteFibers
