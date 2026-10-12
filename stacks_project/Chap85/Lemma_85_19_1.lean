/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_19_1_Slice

/-!
# Lemma 85.19.1

Let `C` be a site with fibre products and `X` an object of `C`. Let `K` be a
hypercovering of `X`. Then `a⁻¹ : Sh(C / X) ⥤ Sh((C / K)_total)` is fully faithful
with essential image the cartesian sheaves of sets, `a⁻¹ : Ab(C / X) ⥤
Ab((C / K)_total)` is fully faithful with essential image the cartesian sheaves of
abelian groups, and in both cases `a_*` is a quasi-inverse.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SemiRepresentableFamily
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C]
variable [HasPullbacks C]
variable (J : GrothendieckTopology C) (X : C) (K : Hypercovering.{w} J X)
variable [HasWeakSheafify (J.over X) (Type (max w u v))]
variable [HasWeakSheafify (overSiteTotalTopology (J.over X) K.toSimplicialObject)
    (Type (max w u v))]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify
      (overSitePrecoverage (J.over X) K.toSimplicialObject n).toGrothendieck
      (Type (max w u v))]
variable [∀ P : (Grothendieck (overSiteDiagram K.toSimplicialObject))ᵒᵖ ⥤
    Type (max w u v),
    (totalForget K.toSimplicialObject).op.HasPointwiseRightKanExtension P]

/-- Lemma 85.19.1 (1): Let `C` be a site with fibre products and `X` an object of
`C`. Let `K` be a hypercovering of `X`. Then `a⁻¹ : Sh(C / X) ⥤ Sh((C / K)_total)`
is fully faithful with essential image the cartesian sheaves of sets, and `a_*`
provides the quasi-inverse functor. -/
@[stacks 0D8K]
def sheafCartesianEquivalence :
    Sheaf (J.over X) (Type (max w u v)) ≌
      Cartesian (J.over X) K.toSimplicialObject (Type (max w u v)) :=
  cartesianEquivalence J X K (Type (max w u v))

/-- The forward functor of `sheafCartesianEquivalence` is `a⁻¹` corestricted to
cartesian sheaves of sets. -/
theorem sheafCartesianEquivalence_functor :
    (sheafCartesianEquivalence J X K).functor =
      cartesianFunctor.{w, v, max u v} (J.over X) (toSliceTerminal J X K)
        (Type (max w u v)) :=
  sorry

/-- The inverse functor of `sheafCartesianEquivalence` is `a_*` on cartesian sheaves
of sets. -/
theorem sheafCartesianEquivalence_inverse :
    (sheafCartesianEquivalence J X K).inverse =
      cartesianInverse.{w, v, max u v} (J.over X) (toSliceTerminal J X K)
        (Type (max w u v)) :=
  sorry

/-- A sheaf of sets on `(C / K)_total` lies in the essential image of `a⁻¹` if and
only if it is cartesian. -/
theorem sheaf_mem_essImage_iff_isCartesian
    (G : Sheaf (overSiteTotalTopology (J.over X) K.toSimplicialObject)
      (Type (max w u v))) :
    (inverseImage (J.over X) K.toSimplicialObject (Type (max w u v))).essImage G ↔
      IsCartesian (J.over X) K.toSimplicialObject (Type (max w u v)) G :=
  sorry

variable [HasWeakSheafify (J.over X) AddCommGrpCat.{max w u v}]
variable [HasWeakSheafify (overSiteTotalTopology (J.over X) K.toSimplicialObject)
    AddCommGrpCat.{max w u v}]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify
      (overSitePrecoverage (J.over X) K.toSimplicialObject n).toGrothendieck
      AddCommGrpCat.{max w u v}]
variable [∀ P : (Grothendieck (overSiteDiagram K.toSimplicialObject))ᵒᵖ ⥤
    AddCommGrpCat.{max w u v},
    (totalForget K.toSimplicialObject).op.HasPointwiseRightKanExtension P]

/-- Lemma 85.19.1 (2): Let `C` be a site with fibre products and `X` an object of
`C`. Let `K` be a hypercovering of `X`. Then `a⁻¹ : Ab(C / X) ⥤ Ab((C / K)_total)`
is fully faithful with essential image the cartesian sheaves of abelian groups, and
`a_*` provides the quasi-inverse functor. -/
@[stacks 0D8K]
def abelianCartesianEquivalence :
    Sheaf (J.over X) AddCommGrpCat.{max w u v} ≌
      Cartesian (J.over X) K.toSimplicialObject AddCommGrpCat.{max w u v} :=
  cartesianEquivalence J X K AddCommGrpCat.{max w u v}

/-- The forward functor of `abelianCartesianEquivalence` is `a⁻¹` corestricted to
cartesian sheaves of abelian groups. -/
theorem abelianCartesianEquivalence_functor :
    (abelianCartesianEquivalence J X K).functor =
      cartesianFunctor.{w, v, max u v} (J.over X) (toSliceTerminal J X K)
        AddCommGrpCat.{max w u v} :=
  sorry

/-- The inverse functor of `abelianCartesianEquivalence` is `a_*` on cartesian
sheaves of abelian groups. -/
theorem abelianCartesianEquivalence_inverse :
    (abelianCartesianEquivalence J X K).inverse =
      cartesianInverse.{w, v, max u v} (J.over X) (toSliceTerminal J X K)
        AddCommGrpCat.{max w u v} :=
  sorry

/-- An abelian sheaf on `(C / K)_total` lies in the essential image of `a⁻¹` if and
only if it is cartesian. -/
theorem abelian_mem_essImage_iff_isCartesian
    (G : Sheaf (overSiteTotalTopology (J.over X) K.toSimplicialObject)
      AddCommGrpCat.{max w u v}) :
    (inverseImage (J.over X) K.toSimplicialObject AddCommGrpCat.{max w u v}).essImage
      G ↔
      IsCartesian (J.over X) K.toSimplicialObject AddCommGrpCat.{max w u v} G :=
  sorry

end CategoryTheory.Hypercovering
