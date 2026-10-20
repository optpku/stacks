/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_17_1_Cartesian
public import stacks_project.Chap85.Lemma_85_17_1_Equivalence

/-!
# Lemma 85.17.1

Let `C` be a site with equalizers and fibre products, and let `K` be a hypercovering.
Then `a⁻¹ : Sh(C) ⥤ Sh((C / K)_total)` is fully faithful with essential image the cartesian
sheaves of sets, `a⁻¹ : Ab(C) ⥤ Ab((C / K)_total)` is fully faithful with essential image
the cartesian sheaves of abelian groups, and in both cases `a_*` is a quasi-inverse.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [HasEqualizers C] [HasPullbacks C]
variable (K : HypercoveringOf.Terminal.{w} J)
variable [HasWeakSheafify J (Type (max w u v))]
variable [HasWeakSheafify (overSiteTotalTopology J K.simplicial) (Type (max w u v))]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify (overSitePrecoverage J K.simplicial n).toGrothendieck (Type (max w u v))]
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤ Type (max w u v),
    (totalForget K.simplicial).op.HasPointwiseRightKanExtension P]

/-- Lemma 85.17.1 (1): Let `C` be a site with equalizers and fibre products. Let `K` be a
hypercovering. Then `a⁻¹ : Sh(C) ⥤ Sh((C / K)_total)` is fully faithful with essential image
the cartesian sheaves of sets, and `a_*` provides the quasi-inverse functor. -/
@[stacks 0D8E]
def sheafCartesianEquivalence :
    Sheaf J (Type (max w u v)) ≌ Cartesian J K.simplicial (Type (max w u v)) :=
  cartesianEquivalence J K (Type (max w u v))

/-- The forward functor of `sheafCartesianEquivalence` is `a⁻¹` corestricted to cartesian
sheaves of sets. -/
theorem sheafCartesianEquivalence_functor :
    (sheafCartesianEquivalence J K).functor =
      cartesianFunctor J K (Type (max w u v)) :=
  sorry

/-- The inverse functor of `sheafCartesianEquivalence` is `a_*` on cartesian sheaves of
sets. -/
theorem sheafCartesianEquivalence_inverse :
    (sheafCartesianEquivalence J K).inverse =
      cartesianInverse J K (Type (max w u v)) :=
  sorry

/-- A sheaf of sets on `(C / K)_total` lies in the essential image of `a⁻¹` if and only if it
is cartesian. -/
theorem sheaf_mem_essImage_iff_isCartesian
    (G : Sheaf (overSiteTotalTopology J K.simplicial) (Type (max w u v))) :
    (inverseImage J K.simplicial (Type (max w u v))).essImage G ↔
      IsCartesian J K.simplicial (Type (max w u v)) G :=
  sorry

variable [HasWeakSheafify J AddCommGrpCat.{max w u v}]
variable [HasWeakSheafify (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify (overSitePrecoverage J K.simplicial n).toGrothendieck
      AddCommGrpCat.{max w u v}]
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
    (totalForget K.simplicial).op.HasPointwiseRightKanExtension P]

/-- Lemma 85.17.1 (2): Let `C` be a site with equalizers and fibre products. Let `K` be a
hypercovering. Then `a⁻¹ : Ab(C) ⥤ Ab((C / K)_total)` is fully faithful with essential image
the cartesian sheaves of abelian groups, and `a_*` provides the quasi-inverse functor. -/
@[stacks 0D8E]
def abelianCartesianEquivalence :
    Sheaf J AddCommGrpCat.{max w u v} ≌
      Cartesian J K.simplicial AddCommGrpCat.{max w u v} :=
  cartesianEquivalence J K AddCommGrpCat.{max w u v}

/-- The forward functor of `abelianCartesianEquivalence` is `a⁻¹` corestricted to cartesian
sheaves of abelian groups. -/
theorem abelianCartesianEquivalence_functor :
    (abelianCartesianEquivalence J K).functor =
      cartesianFunctor J K AddCommGrpCat.{max w u v} :=
  sorry

/-- The inverse functor of `abelianCartesianEquivalence` is `a_*` on cartesian sheaves of
abelian groups. -/
theorem abelianCartesianEquivalence_inverse :
    (abelianCartesianEquivalence J K).inverse =
      cartesianInverse J K AddCommGrpCat.{max w u v} :=
  sorry

/-- An abelian sheaf on `(C / K)_total` lies in the essential image of `a⁻¹` if and only if it
is cartesian. -/
theorem abelian_mem_essImage_iff_isCartesian
    (G : Sheaf (overSiteTotalTopology J K.simplicial) AddCommGrpCat.{max w u v}) :
    (inverseImage J K.simplicial AddCommGrpCat.{max w u v}).essImage G ↔
      IsCartesian J K.simplicial AddCommGrpCat.{max w u v} G :=
  sorry

end CategoryTheory.SemiRepresentableFamily
