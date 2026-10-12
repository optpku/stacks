/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Sites.Continuous
public import stacks_project.Chap59.Lemma_59_54_1
public import stacks_project.Chap63.Lemma_63_3_4_LowerShriek

/-!
# Composition of compact-support étale direct images

The underived identification `g_! ∘ f_! = (f ≫ g)_!` as subsheaves of
`(f ≫ g)_*`, for composable separated locally finite-type morphisms.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The site isomorphism identifying small-étale base change along `g` then `f`
with base change along `f ≫ g`. -/
def smallEtalePullbackCompIso :
    smallEtalePullback g ⋙ smallEtalePullback f ≅ smallEtalePullback (f ≫ g) :=
  (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g).symm

/-- `smallEtalePullbackCompIso` is inverted by its inverse. -/
theorem smallEtalePullbackCompIso_hom_inv_id :
    (smallEtalePullbackCompIso f g).hom ≫ (smallEtalePullbackCompIso f g).inv =
      𝟙 (smallEtalePullback g ⋙ smallEtalePullback f) :=
  sorry

/-- Direct image of abelian small-étale sheaves identifies `g_* ∘ f_*` with
`(f ≫ g)_*`. -/
def etaleAbelianPushforwardCompIso :
    etaleAbelianPushforward f ⋙ etaleAbelianPushforward g ≅
      etaleAbelianPushforward (f ≫ g) :=
  sheafPushforwardContinuousComp' (smallEtalePullbackCompIso f g) AddCommGrpCat.{u}
    Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology

/-- The composition isomorphism of abelian pushforwards is continuous sheaf
pushforward along `smallEtalePullbackCompIso`. -/
theorem etaleAbelianPushforwardCompIso_eq :
    etaleAbelianPushforwardCompIso f g =
      sheafPushforwardContinuousComp' (smallEtalePullbackCompIso f g)
        AddCommGrpCat.{u} Z.smallEtaleTopology Y.smallEtaleTopology
        X.smallEtaleTopology :=
  sorry

variable [IsSeparated f] [LocallyOfFiniteType f]
variable [IsSeparated g] [LocallyOfFiniteType g]

/-- The comparison `X_W ⟶ Y_W` induced by `f` over an étale `Z`-scheme `W`. -/
def baseChangeToMid (W : Z.Etale) :
    ((smallEtalePullback (f ≫ g)).obj W).left ⟶
      ((smallEtalePullback g).obj W).left :=
  pullback.lift (pullback.fst W.hom (f ≫ g))
    (pullback.snd W.hom (f ≫ g) ≫ f) sorry

/-- `baseChangeToMid` is the pullback lift of `X_W ⟶ W` and `X_W ⟶ X ⟶ Y`. -/
theorem baseChangeToMid_fst (W : Z.Etale) :
    baseChangeToMid f g W ≫ pullback.fst W.hom g =
      pullback.fst W.hom (f ≫ g) :=
  sorry

/-- The inclusion of `g_! (f_! F)` into `(f ≫ g)_* F`, as a natural
transformation of functors on abelian small-étale sheaves. -/
def etaleLowerShriekCompι :
    etaleLowerShriek f ⋙ etaleLowerShriek g ⟶ etaleAbelianPushforward (f ≫ g) :=
  whiskerLeft (etaleLowerShriek f) (etaleLowerShriekι g) ≫
    whiskerRight (etaleLowerShriekι f) (etaleAbelianPushforward g) ≫
    (etaleAbelianPushforwardCompIso f g).hom

/-- Objectwise, `etaleLowerShriekCompι` is `g_! f_! ↪ g_* f_! ↪ g_* f_* ≅ (f ≫ g)_*`. -/
theorem etaleLowerShriekCompι_app (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleLowerShriekCompι f g).app F =
      (etaleLowerShriekι g).app ((etaleLowerShriek f).obj F) ≫
        (etaleAbelianPushforward g).map ((etaleLowerShriekι f).app F) ≫
        (etaleAbelianPushforwardCompIso f g).hom.app F :=
  sorry

/-- The subgroup of `((f ≫ g)_* F)(W)` obtained by viewing the sections of
`g_! (f_! F)` on `W` inside `(f ≫ g)_* F`. -/
def etaleLowerShriekCompSections (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (W : Z.Etale) :
    AddSubgroup (F.obj.obj (op ((smallEtalePullback (f ≫ g)).obj W))) :=
  AddSubgroup.map
    (AddCommGrpCat.Hom.hom
      (((etaleLowerShriekCompι f g).app F).hom.app (op W))) ⊤

/-- Membership in the transported `g_! f_!` subgroup is being in the image of
`etaleLowerShriekCompι` on sections over `W`. -/
theorem mem_etaleLowerShriekCompSections_iff
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (W : Z.Etale)
    (σ : F.obj.obj (op ((smallEtalePullback (f ≫ g)).obj W))) :
    σ ∈ etaleLowerShriekCompSections f g F W ↔
      ∃ τ : compactSupportSections g ((etaleLowerShriek f).obj F) W,
        ((etaleLowerShriekCompι f g).app F).hom.app (op W) τ = σ :=
  sorry

/-- The image of a closed subset `T ⊆ X_W` in `Y_W` is closed when `T` is proper
over `Y_W`. -/
theorem isClosed_baseChangeToMid_image (W : Z.Etale)
    (T : TopologicalSpace.Closeds ((smallEtalePullback (f ≫ g)).obj W).left)
    (hT : ClosedSubset.IsProperOver (baseChangeToMid f g W) T) :
    IsClosed (baseChangeToMid f g W '' (T : Set _)) :=
  sorry

/-- A closed subset `T ⊆ X_W` is proper over `W` if and only if it is proper over
`Y_W` and the image of `T` in `Y_W` is a closed subset proper over `W`. -/
theorem isProperOver_baseChange_comp_iff (W : Z.Etale)
    (T : TopologicalSpace.Closeds ((smallEtalePullback (f ≫ g)).obj W).left) :
    ClosedSubset.IsProperOver (pullback.fst W.hom (f ≫ g)) T ↔
      ClosedSubset.IsProperOver (baseChangeToMid f g W) T ∧
        ∃ h : IsClosed (baseChangeToMid f g W '' (T : Set _)),
          ClosedSubset.IsProperOver (pullback.fst W.hom g)
            ⟨baseChangeToMid f g W '' T, h⟩ :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
