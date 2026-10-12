/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Diagram.Basic

/-!
# Constant and reindexed based saturation diagrams

This leaf owns the two basic ways to construct a based diagram from existing
stage data.  Their computation rules are grouped under the corresponding
constructor for direct use by scheduled towers and prefixes.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r' z z' z''

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace Stage.Diagram

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {J : GrothendieckTopology C}
variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}
variable {A : Stage.{u, v, q, r, r'} (J := J) S P x y}
variable {κ : Type z} [Preorder κ]

namespace constant

/-- The constant family of a fixed stage morphism is natural between constant stage functors. -/
theorem naturality
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (f : A ⟶ B) {i j : κ} (g : i ⟶ j) :
    ((Functor.const κ).obj A).map g ≫ f =
      f ≫ ((Functor.const κ).obj B).map g := sorry

end constant

/-- The constant based diagram on one target stage and one compatible refinement. -/
noncomputable def constant
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (f : A ⟶ B) :
    Diagram (J := J) A κ where
  functor := (Functor.const κ).obj B
  base := {
    app := fun _ => f
    naturality := fun _ _ g => constant.naturality B f g
  }

namespace constant

/-- Every stage of a constant based diagram is its chosen target stage. -/
@[simp]
theorem stage
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (f : A ⟶ B) (i : κ) :
    (constant (J := J) (A := A) (κ := κ) B f).stage i = B := sorry

/-- Every transition of a constant based diagram is the identity of its target stage. -/
@[simp]
theorem hom
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (f : A ⟶ B) {i j : κ} (hij : i ≤ j) :
    (constant (J := J) (A := A) (κ := κ) B f).hom hij = 𝟙 B := sorry

/-- Every base leg of a constant based diagram is its chosen stage morphism. -/
@[simp]
theorem fromBase
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (f : A ⟶ B) (i : κ) :
    (constant (J := J) (A := A) (κ := κ) B f).fromBase i = f := sorry

end constant

namespace reindex

/-- Base refinements remain natural after reindexing a based diagram along a monotone map. -/
theorem naturality {κ' : Type z'} [Preorder κ']
    (D : Diagram (J := J) A κ') (f : κ →o κ')
    {i j : κ} (g : i ⟶ j) :
    ((Functor.const κ).obj A).map g ≫ D.fromBase (f j) =
      D.fromBase (f i) ≫ (f.toFunctor ⋙ D.functor).map g := sorry

end reindex

/-- Reindex a based saturation-stage diagram along an order homomorphism. -/
noncomputable def reindex {κ' : Type z'} [Preorder κ']
    (D : Diagram (J := J) A κ') (f : κ →o κ') :
    Diagram (J := J) A κ where
  functor := f.toFunctor ⋙ D.functor
  base := {
    app := fun i => D.fromBase (f i)
    naturality := fun _ _ g => reindex.naturality D f g
  }

namespace reindex

/-- The stage of a reindexed based diagram is the original stage at the image index. -/
@[simp]
theorem stage {κ' : Type z'} [Preorder κ']
    (D : Diagram (J := J) A κ') (f : κ →o κ') (i : κ) :
    (reindex D f).stage i = D.stage (f i) := sorry

/-- A transition of a reindexed based diagram is the original transition at the mapped
comparison. -/
@[simp]
theorem hom {κ' : Type z'} [Preorder κ']
    (D : Diagram (J := J) A κ') (f : κ →o κ')
    {i j : κ} (hij : i ≤ j) :
    (reindex D f).hom hij = D.hom (f.monotone hij) := sorry

/-- A base leg of a reindexed based diagram is the original base leg at the image index. -/
@[simp]
theorem fromBase {κ' : Type z'} [Preorder κ']
    (D : Diagram (J := J) A κ') (f : κ →o κ') (i : κ) :
    (reindex D f).fromBase i = D.fromBase (f i) := sorry

/-- Reindexing a based diagram along the identity order homomorphism changes
no data. -/
@[simp]
theorem id (D : Diagram (J := J) A κ) :
    reindex D OrderHom.id = D := sorry

/-- Successive reindexings agree with reindexing along the composite order
homomorphism. -/
@[simp]
theorem comp {κ' : Type z'} {κ'' : Type z''}
    [Preorder κ'] [Preorder κ''] (D : Diagram (J := J) A κ'')
    (f : κ' →o κ'') (g : κ →o κ') :
    reindex (reindex D f) g = reindex D (f.comp g) := sorry

end reindex

end Stage.Diagram
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
