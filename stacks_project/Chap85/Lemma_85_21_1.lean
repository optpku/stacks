/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.Hypercovering.Augmented
public import stacks_project.Chap85.Lemma_85_19_1

/-!
# Lemma 85.21.1

Let `C` be a site with fibre products and `X` an object of `C`. Let `a : U ⟶ X`
be a hypercovering of `X` in `C`. Then `a⁻¹ : Sh(C / X) ⥤ Sh((C / U)_total)` is
fully faithful with essential image the cartesian sheaves of sets,
`a⁻¹ : Ab(C / X) ⥤ Ab((C / U)_total)` is fully faithful with essential image the
cartesian sheaves of abelian groups, and in both cases `a_*` is a quasi-inverse.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SemiRepresentableFamily
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C]
variable [HasPullbacks C]
variable (J : GrothendieckTopology C) (A : SimplicialObject.Augmented C)
variable (hA : A.IsHypercovering J)
variable [HasWeakSheafify (J.over A.right) (Type (max w u v))]
variable [HasWeakSheafify
    (overSiteTotalTopology (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject)
    (Type (max w u v))]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify
      (overSitePrecoverage (J.over A.right)
          (toHypercovering.{w} A hA).toSimplicialObject n).toGrothendieck
      (Type (max w u v))]
variable [∀ P : (Grothendieck
      (overSiteDiagram (toHypercovering.{w} A hA).toSimplicialObject))ᵒᵖ ⥤
      Type (max w u v),
    (totalForget (toHypercovering.{w} A hA).toSimplicialObject).op.HasPointwiseRightKanExtension P]

/-- Lemma 85.21.1 (1): Let `C` be a site with fibre products and `X` an object of
`C`. Let `a : U ⟶ X` be a hypercovering of `X` in `C`. Then
`a⁻¹ : Sh(C / X) ⥤ Sh((C / U)_total)` is fully faithful with essential image the
cartesian sheaves of sets, and `a_*` provides the quasi-inverse functor. -/
@[stacks 0DA8]
def sheafCartesianEquivalence :
    Sheaf (J.over A.right) (Type (max w u v)) ≌
      Cartesian (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject
        (Type (max w u v)) :=
  Hypercovering.sheafCartesianEquivalence J A.right (toHypercovering.{w} A hA)

/-- The forward functor of `sheafCartesianEquivalence` is `a⁻¹` corestricted to
cartesian sheaves of sets. -/
theorem sheafCartesianEquivalence_functor :
    (sheafCartesianEquivalence J A hA).functor =
      cartesianFunctor.{w, v, max u v} (J.over A.right)
        (Hypercovering.toSliceTerminal J A.right (toHypercovering.{w} A hA))
        (Type (max w u v)) :=
  sorry

/-- The inverse functor of `sheafCartesianEquivalence` is `a_*` on cartesian sheaves
of sets. -/
theorem sheafCartesianEquivalence_inverse :
    (sheafCartesianEquivalence J A hA).inverse =
      cartesianInverse.{w, v, max u v} (J.over A.right)
        (Hypercovering.toSliceTerminal J A.right (toHypercovering.{w} A hA))
        (Type (max w u v)) :=
  sorry

/-- A sheaf of sets on `(C / U)_total` lies in the essential image of `a⁻¹` if and
only if it is cartesian. -/
theorem sheaf_mem_essImage_iff_isCartesian
    (G : Sheaf
      (overSiteTotalTopology (J.over A.right)
        (toHypercovering.{w} A hA).toSimplicialObject)
      (Type (max w u v))) :
    (inverseImage (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject
      (Type (max w u v))).essImage G ↔
      IsCartesian (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject
        (Type (max w u v)) G :=
  sorry

variable [HasWeakSheafify (J.over A.right) AddCommGrpCat.{max w u v}]
variable [HasWeakSheafify
    (overSiteTotalTopology (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject)
    AddCommGrpCat.{max w u v}]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify
      (overSitePrecoverage (J.over A.right)
          (toHypercovering.{w} A hA).toSimplicialObject n).toGrothendieck
      AddCommGrpCat.{max w u v}]
variable [∀ P : (Grothendieck
      (overSiteDiagram (toHypercovering.{w} A hA).toSimplicialObject))ᵒᵖ ⥤
      AddCommGrpCat.{max w u v},
    (totalForget (toHypercovering.{w} A hA).toSimplicialObject).op.HasPointwiseRightKanExtension P]

/-- Lemma 85.21.1 (2): Let `C` be a site with fibre products and `X` an object of
`C`. Let `a : U ⟶ X` be a hypercovering of `X` in `C`. Then
`a⁻¹ : Ab(C / X) ⥤ Ab((C / U)_total)` is fully faithful with essential image the
cartesian sheaves of abelian groups, and `a_*` provides the quasi-inverse functor. -/
@[stacks 0DA8]
def abelianCartesianEquivalence :
    Sheaf (J.over A.right) AddCommGrpCat.{max w u v} ≌
      Cartesian (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject
        AddCommGrpCat.{max w u v} :=
  Hypercovering.abelianCartesianEquivalence J A.right (toHypercovering.{w} A hA)

/-- The forward functor of `abelianCartesianEquivalence` is `a⁻¹` corestricted to
cartesian sheaves of abelian groups. -/
theorem abelianCartesianEquivalence_functor :
    (abelianCartesianEquivalence J A hA).functor =
      cartesianFunctor.{w, v, max u v} (J.over A.right)
        (Hypercovering.toSliceTerminal J A.right (toHypercovering.{w} A hA))
        AddCommGrpCat.{max w u v} :=
  sorry

/-- The inverse functor of `abelianCartesianEquivalence` is `a_*` on cartesian
sheaves of abelian groups. -/
theorem abelianCartesianEquivalence_inverse :
    (abelianCartesianEquivalence J A hA).inverse =
      cartesianInverse.{w, v, max u v} (J.over A.right)
        (Hypercovering.toSliceTerminal J A.right (toHypercovering.{w} A hA))
        AddCommGrpCat.{max w u v} :=
  sorry

/-- An abelian sheaf on `(C / U)_total` lies in the essential image of `a⁻¹` if and
only if it is cartesian. -/
theorem abelian_mem_essImage_iff_isCartesian
    (G : Sheaf
      (overSiteTotalTopology (J.over A.right)
        (toHypercovering.{w} A hA).toSimplicialObject)
      AddCommGrpCat.{max w u v}) :
    (inverseImage (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject
      AddCommGrpCat.{max w u v}).essImage G ↔
      IsCartesian (J.over A.right) (toHypercovering.{w} A hA).toSimplicialObject
        AddCommGrpCat.{max w u v} G :=
  sorry

end CategoryTheory.SimplicialObject.Augmented
