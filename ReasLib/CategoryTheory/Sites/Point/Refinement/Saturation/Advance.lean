/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Stage.Category

/-!
# One-step saturation advances

This leaf packages a reusable choice of a further saturation stage for every
current stage.  It records no recursion, no original Chapter 7 presentation,
and no chosen index order beyond the data already carried by a saturation
stage.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r' w'

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {J : GrothendieckTopology C}

variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}

/-- A uniform one-step saturation choice on the category of scheduled separating
stages.  Each successor map realizes every finite-cover request already present at its source
target. -/
structure Advance where
  /-- The chosen further saturation stage. -/
  next : Stage.{u, v, q, r, r'} (J := J) S P x y →
    Stage.{u, v, q, r, r'} (J := J) S P x y
  /-- The compatible refinement to the chosen further stage. -/
  hom : ∀ A : Stage.{u, v, q, r, r'} (J := J) S P x y, A ⟶ next A
  /-- The successor morphism realizes every request at its source target. -/
  realizes : ∀ A : Stage.{u, v, q, r, r'} (J := J) S P x y,
    (hom A).realizesAll

namespace Advance

/-- Two saturation advances agree when their chosen successor stages and
successor morphisms agree.  The realization field is proof-valued. -/
@[ext]
theorem ext
    {advance advance' : Advance (J := J) (S := S) (P := P) (x := x) (y := y)}
    (h_next : advance.next = advance'.next)
    (h_hom : HEq advance.hom advance'.hom) :
    advance = advance' := sorry

/-- Assemble an advance from a stagewise terminal-refinement existence statement.  The concrete
successor stages and maps are chosen here once, so downstream recursion consumes a single
structured datum rather than nested existential choices. -/
noncomputable def ofExists
    (existsNext :
      ∀ A : Stage.{u, v, q, r, r'} (J := J) S P x y,
        ∃ B : Stage.{u, v, q, r, r'} (J := J) S P x y,
          ∃ f : A ⟶ B, f.realizesAll) :
    Advance (J := J) (S := S) (P := P) (x := x) (y := y) where
  next := fun A => Classical.choose (existsNext A)
  hom := fun A => Classical.choose (Classical.choose_spec (existsNext A))
  realizes := fun A => Classical.choose_spec (Classical.choose_spec (existsNext A))

namespace ofExists

/-- The successor map selected by `ofExists` realizes every request at its source target.  This
is the stable specification of the chosen map; consumers need not unfold the existential
choices. -/
@[simp]
theorem realizes
    (existsNext :
      ∀ A : Stage.{u, v, q, r, r'} (J := J) S P x y,
        ∃ B : Stage.{u, v, q, r, r'} (J := J) S P x y,
          ∃ f : A ⟶ B, f.realizesAll)
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y) :
    ((ofExists (J := J) (S := S) (P := P) (x := x) (y := y) existsNext).hom A).realizesAll := sorry

end ofExists

/-- Recover the stagewise existence statement carried by a uniform saturation advance. -/
theorem toExists (advance : Advance (J := J) (S := S) (P := P) (x := x) (y := y)) :
    ∀ A : Stage.{u, v, q, r, r'} (J := J) S P x y,
      ∃ B : Stage.{u, v, q, r, r'} (J := J) S P x y,
        ∃ f : A ⟶ B, f.realizesAll := sorry

end Advance
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
