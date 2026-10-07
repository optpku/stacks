module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import stacks_project.Chap07.Definition_7_14_1
public import stacks_project.Chap85.Situation_85_3_3_MorphismDiagram

/-!
# Augmentations of covariant simplicial diagrams of sites

An augmentation towards a site `D` in the morphism-of-sites presentation is a
presenting functor `u0 : D ⥤ C.obj ⦋0⦌` which is an exact morphism of sites and
equalizes all simplex operators `φ : ⦋0⦌ ⟶ n`.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace CategoryTheory.SimplicialSites

section

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : D ⥤ C.obj ⦋0⦌)
variable [HasWeakSheafify (J ⦋0⦌).toGrothendieck (Type w)]
variable [∀ P : Dᵒᵖ ⥤ Type w, u0.op.HasLeftKanExtension P]

/-- An augmentation towards a site `D` in the covariant morphism-of-sites
presentation: `u0` presents a morphism of sites `C.obj ⦋0⦌ ⟶ D`, and the
composites `u_φ ∘ u0` are independent of `φ : ⦋0⦌ ⟶ n`. -/
class IsAugmentation : Prop where
  /-- `u0` is an exact morphism of sites from `(D, K)` to `(C.obj ⦋0⦌, J ⦋0⦌)`. -/
  isExactMorphism :
    IsExactMorphismOfSites K.toGrothendieck (J ⦋0⦌).toGrothendieck u0
  /-- The composites `u_φ ∘ u0` agree for all `φ, ψ : ⦋0⦌ ⟶ n`. -/
  map_eq : ∀ {n : SimplexCategory} (φ ψ : ⦋0⦌ ⟶ n),
    u0 ⋙ (C.map φ).toFunctor = u0 ⋙ (C.map ψ).toFunctor

/-- An exact morphism of sites `u0` is an augmentation iff it equalizes every pair
of operators `φ, ψ : ⦋0⦌ ⟶ n`. -/
theorem IsAugmentation.iff :
    IsAugmentation C J K u0 ↔
      IsExactMorphismOfSites K.toGrothendieck (J ⦋0⦌).toGrothendieck u0 ∧
        ∀ {n : SimplexCategory} (φ ψ : ⦋0⦌ ⟶ n),
          u0 ⋙ (C.map φ).toFunctor = u0 ⋙ (C.map ψ).toFunctor :=
  sorry

variable [h_aug : IsAugmentation C J K u0]
include h_aug

/-- An augmentation functor is an exact morphism of sites. -/
instance IsAugmentation.instIsExactMorphismOfSites :
    IsExactMorphismOfSites K.toGrothendieck (J ⦋0⦌).toGrothendieck u0 :=
  h_aug.isExactMorphism

/-- The sheaf inverse image along an augmentation functor preserves finite limits. -/
instance IsAugmentation.instSheafPullbackPreservesFiniteLimits :
    PreservesFiniteLimits
      (u0.sheafPullback (Type w) K.toGrothendieck (J ⦋0⦌).toGrothendieck) :=
  h_aug.isExactMorphism.preservesFiniteLimits_sheafPullback

/-- The two face operators `δ 0, δ 1 : ⦋0⦌ ⟶ ⦋1⦌` yield the same composite with `u0`. -/
theorem IsAugmentation.face_eq :
    u0 ⋙ (C.map (SimplexCategory.δ 0 : ⦋0⦌ ⟶ ⦋1⦌)).toFunctor =
      u0 ⋙ (C.map (SimplexCategory.δ 1 : ⦋0⦌ ⟶ ⦋1⦌)).toFunctor :=
  sorry

/-- The common composite `u_n = u_φ ∘ u0` along the constant operator `⦋0⦌ ⟶ n`. -/
def IsAugmentation.stageFunctor (n : SimplexCategory) : D ⥤ C.obj n :=
  u0 ⋙ (C.map (SimplexCategory.const ⦋0⦌ n 0)).toFunctor

/-- Every composite `u_φ ∘ u0` equals the chosen stage functor at `n`. -/
theorem IsAugmentation.stageFunctor_eq {n : SimplexCategory} (φ : ⦋0⦌ ⟶ n) :
    u0 ⋙ (C.map φ).toFunctor = IsAugmentation.stageFunctor C u0 n :=
  sorry

/-- The morphism of topoi `a0 : Sh(C.obj ⦋0⦌) ⟶ Sh(D)` presented by `u0`. -/
noncomputable def IsAugmentation.toposMap :
    MorphismOfTopoiIn K.toGrothendieck (J ⦋0⦌).toGrothendieck :=
  u0.morphismOfTopoiInOfContinuous K.toGrothendieck (J ⦋0⦌).toGrothendieck

end

/-- The identity on a site is an augmentation of the constant simplex diagram. -/
instance IsAugmentation.const {D : Type u} [Category.{v} D] (K : Precoverage D)
    [HasWeakSheafify K.toGrothendieck (Type w)]
    [∀ P : Dᵒᵖ ⥤ Type w, (𝟭 D).op.HasLeftKanExtension P] :
    IsAugmentation ((Functor.const SimplexCategory).obj (Cat.of D)) (fun _ ↦ K) K (𝟭 D) :=
  sorry

end CategoryTheory.SimplicialSites
