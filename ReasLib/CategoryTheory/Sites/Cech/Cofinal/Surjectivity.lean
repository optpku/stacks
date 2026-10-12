/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import ReasLib.CategoryTheory.Sites.Family.Covering
public import ReasLib.CategoryTheory.Sites.Cech.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cofinal Cech vanishing and surjectivity on sections

The vanishing predicate is degree-parametric and applies to additive presheaves.  Its degree-one
specialization is the obstruction-vanishing hypothesis that makes the right map of a short exact
sequence of additive sheaves surjective on sections.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits
open SemiRepresentableFamily.Over

noncomputable section

universe w v u

namespace CategoryTheory.Cech

variable {C : Type u} [Category.{v} C]
variable [UnivLE.{w, v}]

/-- An additive presheaf has cofinally vanishing degree-`p` Cech cohomology at `U` when every
covering family admits a covering refinement on which that cohomology object is zero. -/
@[stacks 03F8 "cofinal degreewise Cech vanishing"]
def VanishesCofinally
    (J : GrothendieckTopology C) (U : C) [HasFiniteProducts (Over U)]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (p : ℕ) : Prop :=
  ∀ {ι : Type w} (V : ι → Over U), (J.over U).CoversTop V →
    ∃ (κ : Type w) (W : κ → Over U),
      (J.over U).CoversTop W ∧
        Refines
          (ofArrows (fun i ↦ (W i).left) fun i ↦ (W i).hom)
          (ofArrows (fun i ↦ (V i).left) fun i ↦ (V i).hom) ∧
        IsZero (cechCohomology U W F p)

namespace VanishesCofinally

/-- A cofinally vanishing presheaf admits a vanishing covering refinement of any given cover. -/
theorem exists_refinement
    {J : GrothendieckTopology C} {U : C} [HasFiniteProducts (Over U)]
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{v}} {p : ℕ}
    (hF : VanishesCofinally.{w, v, u} J U F p)
    {ι : Type w} (V : ι → Over U) (hV : (J.over U).CoversTop V) :
    ∃ (κ : Type w) (W : κ → Over U),
      (J.over U).CoversTop W ∧
        Refines
          (ofArrows (fun i ↦ (W i).left) fun i ↦ (W i).hom)
          (ofArrows (fun i ↦ (V i).left) fun i ↦ (V i).hom) ∧
        IsZero (cechCohomology U W F p) := sorry

end VanishesCofinally

end CategoryTheory.Cech

namespace CategoryTheory.Sheaf.Cech

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [UnivLE.{w, v}]

/-- Cofinal degreewise Cech vanishing for the underlying additive presheaf of a sheaf. -/
abbrev VanishesCofinally
    (F : Sheaf J AddCommGrpCat.{v}) (U : C) [HasFiniteProducts (Over U)] (p : ℕ) : Prop :=
  CategoryTheory.Cech.VanishesCofinally.{w, v, u} J U
    ((sheafToPresheaf J AddCommGrpCat.{v}).obj F) p

namespace VanishesCofinally

/-- If the left term of a short exact sequence has cofinally vanishing first Cech cohomology at
`U`, the map from middle to right sections over `U` is surjective. -/
@[stacks 03F8 "surjectivity on sections from cofinal Cech vanishing"]
theorem surjective_right
    (U : C) [HasFiniteProducts (Over U)]
    (S : ShortComplex (Sheaf J AddCommGrpCat.{v})) (hS : S.ShortExact)
    (hF : VanishesCofinally.{w} S.X₁ U 1) :
    Function.Surjective
      (((sheafSections J AddCommGrpCat.{v}).obj (op U)).map S.g) := sorry

end VanishesCofinally

end CategoryTheory.Sheaf.Cech
