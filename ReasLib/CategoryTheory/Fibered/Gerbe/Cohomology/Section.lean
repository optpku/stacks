module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.CategoryTheory.Sites.Family.Covering
public import ReasLib.CategoryTheory.Fibered.Gerbe.Band
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomological section criterion for abelian gerbes

This leaf owns the cofinal vanishing hypothesis used to kill the local torsor and overlap
obstructions, together with the resulting section-existence statement for an abelian gerbe.  The
degree-parametric predicate is the reusable layer; the long degree-one name is retained only as a
source-facing specialization for Lemma 21.11.1.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits
open SemiRepresentableFamily.Over

noncomputable section

universe w v u uS vS

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace Sheaf.Cech

/-- A sheaf has cofinally vanishing degree-`p` cohomology on the members and pairwise overlaps of
refinements of every covering family of `U`. -/
@[stacks 0CK0 "cofinal vanishing on terms and overlaps"]
def CofinalH
    (G : Sheaf J AddCommGrpCat.{vS}) (U : C)
    [Limits.HasFiniteProducts (Over U)]
    [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{vS}]
    [∀ X : C, HasExt (Sheaf (J.over X) AddCommGrpCat.{vS})]
    (p : ℕ) : Prop :=
  ∀ (ι : Type w) (V : ι → Over U), (J.over U).CoversTop V →
    ∃ (κ : Type w) (W : κ → Over U),
      (J.over U).CoversTop W ∧
        Refines
          (ofArrows (fun i ↦ (W i).left) fun i ↦ (W i).hom)
          (ofArrows (fun i ↦ (V i).left) fun i ↦ (V i).hom) ∧
        (∀ i : κ, IsZero <| AddCommGrpCat.of ((G.over (W i).left).H p)) ∧
        ∀ i j : κ, IsZero <| AddCommGrpCat.of ((G.over ((Limits.prod (W i) (W j)).left)).H p)

namespace CofinalH

/-- A cofinal vanishing hypothesis supplies a refining cover with vanishing terms and overlaps. -/
@[stacks 0CK0 "cofinal vanishing refinement"]
theorem exists_refinement
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}
    [Limits.HasFiniteProducts (Over U)]
    [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{vS}]
    [∀ X : C, HasExt (Sheaf (J.over X) AddCommGrpCat.{vS})]
    {G : Sheaf J AddCommGrpCat.{vS}} (p : ℕ)
    (hG : CofinalH G U p)
    {ι : Type w} (V : ι → Over U) (hV : (J.over U).CoversTop V) :
    ∃ (κ : Type w) (W : κ → Over U),
      (J.over U).CoversTop W ∧
        Refines
          (ofArrows (fun i ↦ (W i).left) fun i ↦ (W i).hom)
          (ofArrows (fun i ↦ (V i).left) fun i ↦ (V i).hom) ∧
        (∀ i : κ, IsZero <| AddCommGrpCat.of ((G.over (W i).left).H p)) ∧
        ∀ i j : κ, IsZero <| AddCommGrpCat.of ((G.over ((Limits.prod (W i) (W j)).left)).H p) := sorry

end CofinalH

end Sheaf.Cech

namespace Sheaf

/-- The source-facing degree-one specialization of `Sheaf.Cech.CofinalH`. -/
@[stacks 0CK0 "cofinal H1 vanishing on terms and overlaps"]
abbrev HasCofinalCoveringsWithVanishingH1OnTermsAndOverlaps
    (G : Sheaf J AddCommGrpCat.{vS}) (U : C)
    [Limits.HasFiniteProducts (Over U)]
    [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{vS}]
    [∀ X : C, HasExt (Sheaf (J.over X) AddCommGrpCat.{vS})] : Prop :=
  Cech.CofinalH.{w} G U 1

end Sheaf

namespace IsGerbe

/-- Lemma 21.11.1 (Tag 0CK0): cofinal H¹-vanishing on terms and overlaps, together with
vanishing H² on `U`, produces an object of the abelian gerbe over `U`. -/
@[stacks 0CK0 "gerbe section from cofinal H1 and H2 vanishing"]
theorem existsSection_of_cofinalH1
    {C : Type u} [Category.{v} C] {S : Type uS} [Category.{vS} S]
    {J : GrothendieckTopology C}
    [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{vS}]
    [∀ X : C, HasExt (Sheaf (J.over X) AddCommGrpCat.{vS})]
    (p : S ⥤ C) [IsGerbe J p]
    [Functor.IsFibered.InGroupoids.Automorphism.IsAbelian p]
    (G : Sheaf J AddCommGrpCat.{vS})
    (hBand : Functor.IsFibered.InGroupoids.IsBand p J G)
    (U : C) [Limits.HasFiniteProducts (Over U)]
    (hcofinal : G.HasCofinalCoveringsWithVanishingH1OnTermsAndOverlaps U)
    (hH2 : IsZero <| AddCommGrpCat.of ((G.over U).H 2)) :
    Nonempty (p.Fiber U) := sorry

end IsGerbe

end CategoryTheory
