/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Truncation of simplicial copowers

This file isolates the restriction API for simplicial copowers.  The generic indexed-coproduct
precomposition instance is the mathematical owner, while low-priority bridges expose it through
Mathlib's bundled truncation presentation and through the canonical truncated constant functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

namespace copower

/-- Restrict a full copower owner through Mathlib's `truncation` presentation.  Typeclass search
does not unfold the `whiskeringLeft.obj` wrapper far enough to use
`Functor.HasIndexedCoprod.comp` directly, so this low-priority instance is the presentation
bridge and owns no new coproduct data. -/
@[stacks 018V "restricted copower existence"]
instance (priority := 40) truncation.hasCopower
    (n : ℕ) (U : SSet.{w}) (V : SimplicialObject C) [HasCopower U V] :
    Truncated.HasCopower ((SSet.truncation n).obj U) ((truncation n).obj V) :=
  Functor.HasIndexedCoprod.comp (SimplexCategory.Truncated.inclusion n).op U V

/-- A full constant simplicial copower canonically supplies the bundled truncated constant
copower.  This bridge is needed because restricting a constant functor and rebuilding the
constant functor are propositionally, but not definitionally, the same owner. -/
@[stacks 018V "restricted constant copower existence"]
instance (priority := 40) truncation.constHasCopower (n : ℕ) (U : SSet.{w}) (X : C)
    [HasCopower U ((const C).obj X)] :
    Truncated.HasCopower ((SSet.truncation n).obj U)
      ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X) :=
  ⟨fun Delta ↦ Functor.HasIndexedCoprod.hasCoproduct
    (U := U) (V := (const C).obj X)
    ((SimplexCategory.Truncated.inclusion n).op.obj Delta)⟩

/-- Truncating a simplicial copower agrees definitionally with the copower of the two
truncations.  The named isomorphism shields downstream code from that presentation detail. -/
@[stacks 018V "truncation of a simplicial copower"]
def truncation.iso (n : ℕ) (U : SSet.{w}) (V : SimplicialObject C)
    [HasCopower U V] :
    (truncation n).obj (copower U V) ≅
      Truncated.copower ((SSet.truncation n).obj U) ((truncation n).obj V) :=
  Iso.refl _

namespace truncation

section IndexHom

variable {U W : SSet.{w}} (n : ℕ) (V : SimplicialObject C)
variable [HasCopower U V] [HasCopower W V]

/-- The component of a reindexing map between truncations of full simplicial copowers. -/
@[stacks 018V "restricted copower reindexing component"]
abbrev indexHom.app
    (a : (SSet.truncation n).obj U ⟶ (SSet.truncation n).obj W)
    (Delta : (SimplexCategory.Truncated n)ᵒᵖ) :
    ((truncation n).obj (copower U V)).obj Delta ⟶
      ((truncation n).obj (copower W V)).obj Delta :=
  Functor.indexedCoprod.indexHomApp ((truncation n).obj V) a Delta

/-- Reindexing maps between restricted full copowers commute with truncated structure maps. -/
@[stacks 018V "restricted copower reindexing naturality"]
theorem indexHom.naturality
    (a : (SSet.truncation n).obj U ⟶ (SSet.truncation n).obj W)
    {Delta Delta' : (SimplexCategory.Truncated n)ᵒᵖ} (f : Delta ⟶ Delta') :
    ((truncation n).obj (copower U V)).map f ≫ indexHom.app n V a Delta' =
      indexHom.app n V a Delta ≫
        ((truncation n).obj (copower W V)).map f := sorry

/-- Reindex truncations of full simplicial copowers by a map of truncated indexing objects. -/
@[stacks 018V "restricted copower reindexing"]
abbrev indexHom
    (a : (SSet.truncation n).obj U ⟶ (SSet.truncation n).obj W) :
    (truncation n).obj (copower U V) ⟶ (truncation n).obj (copower W V) :=
  Functor.indexedCoprod.indexHom ((truncation n).obj V) a

/-- Reindexing a restricted full copower sends each coproduct injection to the injection with the
reindexed label. -/
@[stacks 018V "restricted copower reindexing injection formula"]
theorem indexHom.ι
    (a : (SSet.truncation n).obj U ⟶ (SSet.truncation n).obj W)
    (Delta : (SimplexCategory.Truncated n)ᵒᵖ)
    (x : ((SSet.truncation n).obj U).obj Delta) :
    Sigma.ι
        (fun _ : U.obj ((SimplexCategory.Truncated.inclusion n).op.obj Delta) ↦
          V.obj ((SimplexCategory.Truncated.inclusion n).op.obj Delta)) x ≫
      (indexHom n V a).app Delta =
    Sigma.ι
      (fun _ : W.obj ((SimplexCategory.Truncated.inclusion n).op.obj Delta) ↦
        V.obj ((SimplexCategory.Truncated.inclusion n).op.obj Delta)) (a.app Delta x) := sorry

end IndexHom

end truncation

end copower

end CategoryTheory.SimplicialObject
