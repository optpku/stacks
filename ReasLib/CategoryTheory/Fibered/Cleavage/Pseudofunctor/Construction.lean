/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Cleavage.Pseudofunctor.Coherence
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pseudofunctor associated to a cleavage

The concrete owner is a mathlib `Pseudofunctor`. Its non-Prop data consists of the standard
fibers, chosen reindexing functors, and the canonical unit and composition comparisons.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor.Cleavage

variable {p : S ⥤ C} (χ : p.Cleavage)

/-- The fiber categories, pullback functors, composition comparisons `α_{g,f}`, and unit
comparisons `α_U` assemble into the canonical pseudofunctor `Cᵒᵖ ⥤ᵖ Cat`. -/
@[stacks 02XO "(3)"]
noncomputable def toPseudofunctor :
    LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun U ↦ Cat.of (Fiber p (unop U)))
    (fun f ↦ ((f.unop)⁎[χ]).toCatHom)
    (fun U ↦ Cat.Hom.isoMk ((Reindex.idIso χ (unop U)).symm))
    (fun f g ↦ Cat.Hom.isoMk (Reindex.compIso χ f.unop g.unop))
    (fun f g h ↦ toPseudofunctor.map₂.associator χ f g h)
    (fun f ↦ toPseudofunctor.map₂.leftUnitor χ f)
    (fun f ↦ toPseudofunctor.map₂.rightUnitor χ f)

end Functor.Cleavage

end CategoryTheory
