module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import stacks_project.Chap61.Lemma_61_17_3_Comparison
public import stacks_project.Chap61.Lemma_61_17_4_Comparison
public import stacks_project.Chap61.Remark_61_14_4_Sections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.17.3

Cohomology of a derived abelian sheaf on the big pro-étale site over `S`,
evaluated at `S` or `T`, agrees with cohomology on the corresponding small
pro-étale site after `π_S⁻¹`, `f_small⁻¹`, or `i_f⁻¹`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/-- Lemma 61.17.3 (1): for `K` in `D(S.ProEt)`, the cohomology of `π_S⁻¹ K` on the
big pro-étale site over `S`, evaluated at `S`, agrees with the cohomology of `K`
on the small pro-étale site of `S`. -/
@[stacks 0F69]
theorem proetaleCohomology_piInverseImage (S : Scheme.{u}) (n : ℤ)
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (Sheaf (topology S) AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1})]
    [∀ P : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (ProEt.forget S).op.HasLeftKanExtension P]
    (K : DerivedCategory (Sheaf (topology S) AddCommGrpCat.{u + 1})) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (proetaleTopology.over S) (Over.mk (𝟙 S))).obj
          ((piExact S).mapDerivedCategory.obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (topology S) (globalProEt S)).obj K)) := sorry

/-- Lemma 61.17.3 (2): for a morphism `f : T ⟶ S` and `K` in `D(S.ProEt)`, the
cohomology of `π_S⁻¹ K` on the big pro-étale site over `S`, evaluated at `T`,
agrees with the cohomology of `f_small⁻¹ K` on the small pro-étale site of `T`. -/
@[stacks 0F69]
theorem proetaleCohomology_smallInverseImage {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (Sheaf (topology S) AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf (topology T) AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1})]
    [∀ P : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (ProEt.forget S).op.HasLeftKanExtension P]
    [∀ P : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallProetalePullback f).op.HasLeftKanExtension P]
    (K : DerivedCategory (Sheaf (topology S) AddCommGrpCat.{u + 1})) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (proetaleTopology.over S) (Over.mk f)).obj
          ((piExact S).mapDerivedCategory.obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (topology T) (globalProEt T)).obj
          ((smallInverseImage f).mapDerivedCategory.obj K))) := sorry

/-- Lemma 61.17.3 (3): for a morphism `f : T ⟶ S` and `M` in
`D((Sch/S)_proétale)`, the cohomology of `M` on the big pro-étale site over `S`,
evaluated at `T`, agrees with the cohomology of `i_f⁻¹ M` on the small
pro-étale site of `T`. -/
@[stacks 0F69]
theorem proetaleCohomology_relocalization {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (Sheaf (topology T) AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1})]
    (M : DerivedCategory (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1})) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (proetaleTopology.over S) (Over.mk f)).obj M))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (topology T) (globalProEt T)).obj
          ((iInverseImage f).mapDerivedCategory.obj M))) := sorry

end AlgebraicGeometry.Scheme.ProEt
