/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pro.Presentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sequential pro-morphism representatives

A morphism between pro-objects presented by inverse sequences can be represented by a monotone
reindexing and compatible level maps.  This leaf owns that explicit data and its elementary
refinement, identity, and composition operations.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped CategoryTheory

universe u v

namespace CategoryTheory.Pro

/-
The verified canonical owners `Pro.limHomEquiv`, `Types.jointly_surjective'`, and
`Types.FilteredColimit.colimit_eq_iff` do not package the simultaneous monotone choice needed for
a sequential representative.  The project-local owner therefore stores exactly that data; its
comparison with the canonical pro-Hom belongs to `Sequential.Realization`.
-/

/-- A monotone level presentation of a morphism between
sequential inverse systems:

```
       ⋯ ⟶ X(m 3) ⟶ X(m 2) ⟶ X(m 1)
              │          │          │
              ▼          ▼          ▼
       ⋯ ⟶  Y(3)   ⟶   Y(2)   ⟶   Y(1)
```

Here `X(m n)` abbreviates `X.obj (op (m n))`, and `Y(n)` abbreviates `Y.obj (op n)`.
The natural transformation packages compatibility of all level maps. -/
@[stacks 0G2W "sequential pro-morphism presentations"]
structure SequentialHom {C : Type u} [Category.{v} C]
    (X Y : ℕᵒᵖ ⥤ C) where
  /-- A monotone choice of source stage for each target stage. -/
  reindex : ℕ →o ℕ
  /-- The compatible family of level maps from the reindexed source system to the target. -/
  hom : reindex.toFunctor.op ⋙ X ⟶ Y

namespace SequentialHom

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable {C : Type u} [Category.{v} C] {X Y : ℕᵒᵖ ⥤ C}

/-- Compatibility of the level maps obtained by enlarging every chosen source stage. -/
private theorem refineNaturality (r : SequentialHom X Y)
    (reindex' : ℕ →o ℕ) (hle : r.reindex ≤ reindex')
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (reindex'.toFunctor.op ⋙ X).map f ≫
        (X.map (homOfLE (hle j.unop)).op ≫ r.hom.app j) =
      (X.map (homOfLE (hle i.unop)).op ≫ r.hom.app i) ≫ Y.map f := sorry

/-- Enlarge the chosen source stage of a sequential representative at every target level. -/
def refine (r : SequentialHom X Y) (reindex' : ℕ →o ℕ)
    (hle : r.reindex ≤ reindex') : SequentialHom X Y where
  reindex := reindex'
  hom :=
    { app := fun i ↦ X.map (homOfLE (hle i.unop)).op ≫ r.hom.app i
      naturality := fun _ _ f ↦ refineNaturality r reindex' hle f }

/-- Refinement records the requested enlarged monotone reindexing. -/
@[simp]
theorem refine_reindex (r : SequentialHom X Y) (reindex' : ℕ →o ℕ)
    (hle : r.reindex ≤ reindex') :
    (r.refine reindex' hle).reindex = reindex' := sorry

/-- The level map of a refinement is the source transition to the enlarged stage followed by
the original level map. -/
@[simp]
theorem refine_hom_app (r : SequentialHom X Y) (reindex' : ℕ →o ℕ)
    (hle : r.reindex ≤ reindex') (i : ℕᵒᵖ) :
    (r.refine reindex' hle).hom.app i =
      X.map (homOfLE (hle i.unop)).op ≫ r.hom.app i := sorry

/-- The identity sequential representative uses the identity reindexing and identity level maps. -/
def id (X : ℕᵒᵖ ⥤ C) : SequentialHom X X where
  reindex := OrderHom.id
  hom :=
    { app := fun i ↦ 𝟙 (X.obj i)
      naturality := fun _ _ _ ↦ sorry }

/-- The identity sequential representative uses the identity monotone reindexing. -/
@[simp]
theorem id_reindex (X : ℕᵒᵖ ⥤ C) :
    (id X).reindex = OrderHom.id := sorry

/-- Every level map of the identity sequential representative is an identity morphism. -/
@[simp]
theorem id_hom_app (X : ℕᵒᵖ ⥤ C) (i : ℕᵒᵖ) :
    (id X).hom.app i = 𝟙 (X.obj i) := sorry

/-- Compose sequential representatives by composing their monotone reindexings and the
corresponding level maps. -/
def comp {Z : ℕᵒᵖ ⥤ C} (r : SequentialHom X Y)
    (s : SequentialHom Y Z) : SequentialHom X Z where
  reindex := r.reindex.comp s.reindex
  hom :=
    { app := fun i ↦ r.hom.app (op (s.reindex i.unop)) ≫ s.hom.app i
      naturality := fun _ _ _ ↦ sorry }

/-- Sequential composition composes the two monotone reindexings. -/
@[simp]
theorem comp_reindex {Z : ℕᵒᵖ ⥤ C} (r : SequentialHom X Y)
    (s : SequentialHom Y Z) :
    (comp r s).reindex = r.reindex.comp s.reindex := sorry

/-- The level map of a composite is the composite of the corresponding level maps. -/
@[simp]
theorem comp_hom_app {Z : ℕᵒᵖ ⥤ C} (r : SequentialHom X Y)
    (s : SequentialHom Y Z) (i : ℕᵒᵖ) :
    (comp r s).hom.app i = r.hom.app (op (s.reindex i.unop)) ≫ s.hom.app i := sorry

end SequentialHom

end CategoryTheory.Pro
