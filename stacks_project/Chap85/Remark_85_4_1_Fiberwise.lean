module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import stacks_project.Chap07.Definition_7_20_1_Cocontinuous
public import stacks_project.Chap85.Situation_85_3_3_Fiberwise

/-!
# Augmentations of fiberwise simplicial sites

An augmentation towards a site `D` in the cocontinuous presentation is a
presenting functor `u0 : F.obj (op ⦋0⦌) ⥤ D` which is cocontinuous and equalizes
all simplex operators `φ : ⦋0⦌ ⟶ n` after precomposition.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.Grothendieck

section

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : F.obj (op ⦋0⦌) ⥤ D)

/-- An augmentation towards a site `D` in the cocontinuous presentation: `u0` is
cocontinuous, and the composites `u0 ∘ u_φ` are independent of `φ : ⦋0⦌ ⟶ n`. -/
class IsAugmentation : Prop where
  /-- `u0` is cocontinuous for the chosen stage and target precoverages. -/
  isCocontinuous : Functor.Precoverage.IsCocontinuous u0 (J (op ⦋0⦌)) K
  /-- The composites `u0 ∘ u_φ` agree for all `φ, ψ : ⦋0⦌ ⟶ n`. -/
  map_eq : ∀ {n : SimplexCategory} (φ ψ : ⦋0⦌ ⟶ n),
    (F.map φ.op).toFunctor ⋙ u0 = (F.map ψ.op).toFunctor ⋙ u0

/-- A cocontinuous functor `u0` is an augmentation iff it equalizes every pair
of operators `φ, ψ : ⦋0⦌ ⟶ n` after precomposition. -/
theorem IsAugmentation.iff :
    IsAugmentation F J K u0 ↔
      Functor.Precoverage.IsCocontinuous u0 (J (op ⦋0⦌)) K ∧
        ∀ {n : SimplexCategory} (φ ψ : ⦋0⦌ ⟶ n),
          (F.map φ.op).toFunctor ⋙ u0 = (F.map ψ.op).toFunctor ⋙ u0 :=
  sorry

variable [h_aug : IsAugmentation F J K u0]
include h_aug

/-- An augmentation functor is cocontinuous for the chosen precoverages. -/
instance IsAugmentation.instIsCocontinuous :
    Functor.Precoverage.IsCocontinuous u0 (J (op ⦋0⦌)) K :=
  h_aug.isCocontinuous

/-- The two face operators `δ 0, δ 1 : ⦋0⦌ ⟶ ⦋1⦌` yield the same composite with `u0`. -/
theorem IsAugmentation.face_eq :
    (F.map (SimplexCategory.δ 0 : ⦋0⦌ ⟶ ⦋1⦌).op).toFunctor ⋙ u0 =
      (F.map (SimplexCategory.δ 1 : ⦋0⦌ ⟶ ⦋1⦌).op).toFunctor ⋙ u0 :=
  sorry

/-- The common composite `u_n = u0 ∘ u_φ` along the constant operator `⦋0⦌ ⟶ n`. -/
def IsAugmentation.stageFunctor (n : SimplexCategory) : F.obj (op n) ⥤ D :=
  (F.map (SimplexCategory.const ⦋0⦌ n 0).op).toFunctor ⋙ u0

/-- Every composite `u0 ∘ u_φ` equals the chosen stage functor at `n`. -/
theorem IsAugmentation.stageFunctor_eq {n : SimplexCategory} (φ : ⦋0⦌ ⟶ n) :
    (F.map φ.op).toFunctor ⋙ u0 = IsAugmentation.stageFunctor F u0 n :=
  sorry

variable [K.IsSite] [(J (op ⦋0⦌)).IsSite]
variable [HasSheafify (J (op ⦋0⦌)).toGrothendieck (Type w)]
variable [∀ P : (F.obj (op ⦋0⦌))ᵒᵖ ⥤ Type w, u0.op.HasPointwiseRightKanExtension P]

/-- The morphism of topoi `a0 : Sh(F.obj (op ⦋0⦌)) ⟶ Sh(D)` presented by `u0`. -/
noncomputable def IsAugmentation.toposMap :
    MorphismOfTopoiIn K.toGrothendieck (J (op ⦋0⦌)).toGrothendieck :=
  u0.morphismOfTopoiInOfCocontinuous (J (op ⦋0⦌)).toGrothendieck K.toGrothendieck

end

/-- The identity on a site is an augmentation of the constant simplicial diagram. -/
instance IsAugmentation.const {D : Type u} [Category.{v} D] (K : Precoverage D) :
    IsAugmentation ((Functor.const SimplexCategoryᵒᵖ).obj (Cat.of D)) (fun _ ↦ K) K (𝟭 D) :=
  sorry

end CategoryTheory.Grothendieck
