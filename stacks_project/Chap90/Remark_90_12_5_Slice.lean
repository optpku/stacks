/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Over
import StacksCheckRecall

/-!
# Residue-slice of a category cofibered in groupoids

Slicing a category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` at a
residue-fibre object `x` yields the predeformation category `F_x`. A based
morphism `φ` induces `φ_x : F_x ⟶ G_{φ(x)}`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat Functor
open scoped Bicategory

universe u v w

/- Remark 90.12.5: a based morphism induces a based morphism between the residue
slice at an object and the residue slice at its image. -/
@[stacks 06IK] #check
  (CategoryTheory.BasedFunctor.sliceMap :
    ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k] {F G : Type v} [Category.{w} F] [Category.{w} G]
      {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}
      [IsFibered.InGroupoids p.op] [IsFibered.InGroupoids q.op]
      (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
      (x : p.Fiber (residue Λ k)),
      BasedCategory.ofFunctor (CategoryTheory.Functor.sliceAt p x) ⥤ᵇ
        BasedCategory.ofFunctor
          (CategoryTheory.Functor.sliceAt q (CategoryTheory.BasedFunctor.objAt φ x)))
