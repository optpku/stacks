/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CatCommSq
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Big
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Big
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Basic
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Situation

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open CategoryTheory.Sheaf
open scoped MorphismOfTopoiIn

noncomputable section

universe u i

namespace AlgebraicGeometry.Scheme.PhComparison

/-- The comparison from big ph sheaves to big étale sheaves commutes with
direct image along a morphism of schemes over a fixed base. -/
theorem bigPhEtaleCommSq {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    Nonempty (CatCommSq (Ph.Big.morphismOfTopoi f.left).pushforward
      (standardComparison .etale X.left).pushforward (standardComparison .etale Y.left).pushforward
      (Etale.Big.morphismOfTopoi f.left).pushforward) := sorry

/-- The composite comparison from big ph sheaves to small étale sheaves
commutes with direct image along a morphism of schemes over a fixed base. -/
theorem phSmallEtaleCommSq {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    Nonempty (CatCommSq (Ph.Big.morphismOfTopoi f.left).pushforward
      ((standardComparison .etale X.left).pushforward ⋙
        (Etale.SmallToBig.siteMorphismOfTopoi X.left).pushforward)
      ((standardComparison .etale Y.left).pushforward ⋙
        (Etale.SmallToBig.siteMorphismOfTopoi Y.left).pushforward)
      (Etale.SmallToBig.smallMorphism f.left).pushforward) := sorry

/-- Proper morphisms in the slice category `Over S`. -/
abbrev properOver (S : Scheme.{u}) : MorphismProperty (Over S) :=
  MorphismProperty.over (@IsProper : MorphismProperty Scheme.{u})

/-- A morphism in `Over S` is proper iff its underlying scheme morphism is proper. -/
theorem properOver_iff {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    properOver S f ↔ IsProper f.left := sorry

/-- Proper morphisms in `Over S` admit pullbacks. -/
instance properOver_hasPullbacks (S : Scheme.{u}) :
    (properOver S).HasPullbacks := inferInstance

/-- Proper morphisms in `Over S` are stable under base change. -/
instance properOver_isStableUnderBaseChange (S : Scheme.{u}) :
    (properOver S).IsStableUnderBaseChange := sorry

/-- The big étale topology on `Over S` is coarser than the big ph topology. -/
theorem etale_le_ph (S : Scheme.{u}) :
    S.overGrothendieckTopology @Etale ≤ Scheme.bigPhSite S := sorry

/-- Abelian-group-valued sheafification exists on every iterated étale slice at the
topology-comparison coefficient universe. -/
instance etaleSlice_hasSheafify_addCommGrp {S : Scheme.{u}} (X : Over S) :
    HasSheafify ((S.overGrothendieckTopology @Etale).over X)
      AddCommGrpCat.{u + 1} := sorry

/-- Abelian sheaves on iterated étale slices have injective resolutions at the
topology-comparison coefficient universe. -/
instance etaleSlice_hasInjectiveResolutions {S : Scheme.{u}} (X : Over S) :
    HasInjectiveResolutions
      (Sheaf ((S.overGrothendieckTopology @Etale).over X)
        AddCommGrpCat.{u + 1}) := sorry

/-- Direct image of abelian sheaves along postcomposition on iterated étale slices
is additive. -/
instance overMap_sheafPushforwardCocontinuous_additive
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      ((S.overGrothendieckTopology @Etale).over X)
      ((S.overGrothendieckTopology @Etale).over Y)).Additive := sorry

/-- The site functor `π_X` from the small étale site of `X` to the iterated étale
slice `(Sch/S)_étale / X`. -/
abbrev piSiteFunctor {S : Scheme.{u}} (X : Over S) : X.left.Etale ⥤ Over X :=
  relocalizationFunctor (𝟙 X.left) ⋙ X.iteratedSliceBackward

/-- Forgetting the slice over `X` recovers étale relocalization into `Over S`. -/
theorem piSiteFunctor_forget {S : Scheme.{u}} (X : Over S) :
    piSiteFunctor X ⋙ Over.forget X =
      relocalizationFunctor (𝟙 X.left) ⋙ Over.map X.hom := sorry

/-- The site functor `π_X` is continuous from the small étale topology to the étale
topology on the iterated slice. -/
instance piSiteFunctor_isContinuous {S : Scheme.{u}} (X : Over S) :
    Functor.IsContinuous (piSiteFunctor X) X.left.smallEtaleTopology
      ((S.overGrothendieckTopology @Etale).over X) :=
  Functor.isContinuous_comp (relocalizationFunctor (𝟙 X.left)) X.iteratedSliceBackward
    X.left.smallEtaleTopology (X.left.overGrothendieckTopology @Etale)
    ((S.overGrothendieckTopology @Etale).over X)

/-- Étale relocalization into an iterated slice admits left Kan extensions on
abelian presheaves at the topology-comparison coefficient universe. -/
instance piSiteFunctor_op_hasLeftKanExtension_addCommGrp
    {S : Scheme.{u}} (X : Over S) (P : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (piSiteFunctor X).op.HasLeftKanExtension P := sorry

/-- Inverse image `π_X⁻¹` on abelian sheaves, landing in the étale iterated slice. -/
def piInverseImage {S : Scheme.{u}} (X : Over S) :
    Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf ((S.overGrothendieckTopology @Etale).over X) AddCommGrpCat.{u + 1} :=
  (piSiteFunctor X).sheafPullback AddCommGrpCat.{u + 1}
    X.left.smallEtaleTopology ((S.overGrothendieckTopology @Etale).over X)

/-- Inverse image `π_X⁻¹` is the sheaf pullback along `piSiteFunctor X`. -/
theorem piInverseImage_eq {S : Scheme.{u}} (X : Over S) :
    piInverseImage X =
      (piSiteFunctor X).sheafPullback AddCommGrpCat.{u + 1}
        X.left.smallEtaleTopology ((S.overGrothendieckTopology @Etale).over X) := sorry

/-- The coefficient family `A'_X` of sheaves on `(Sch/X)_étale` of the form `π_X⁻¹ F`
for a torsion abelian sheaf `F` on `X_étale`. -/
abbrev torsionPiInverseImage {S : Scheme.{u}} (X : Over S) :
    ObjectProperty
      (Sheaf ((S.overGrothendieckTopology @Etale).over X) AddCommGrpCat.{u + 1}) :=
  (Sheaf.torsion X.left.smallEtaleTopology).map (piInverseImage X)

/-- Membership in `A'_X` means being isomorphic to `π_X⁻¹ F` for some torsion abelian
sheaf on the small étale site. -/
theorem mem_torsionPiInverseImage_iff {S : Scheme.{u}} {X : Over S}
    {ℱ : Sheaf ((S.overGrothendieckTopology @Etale).over X) AddCommGrpCat.{u + 1}} :
    torsionPiInverseImage X ℱ ↔
      ∃ F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1},
        F.IsLocallyTorsion ∧ Nonempty ((piInverseImage X).obj F ≅ ℱ) := sorry

/-- The inverse image of a torsion small-étale sheaf lies in `A'_X`. -/
theorem obj_mem_torsionPiInverseImage {S : Scheme.{u}} {X : Over S}
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) :
    torsionPiInverseImage X ((piInverseImage X).obj F) := sorry

/-- Each coefficient family `A'_X` is a weak Serre subcategory. -/
instance torsionPiInverseImage_isWeakSerre {S : Scheme.{u}} (X : Over S) :
    IsWeakSerreClass (torsionPiInverseImage X) := sorry

/-- Inverse image along a morphism of the slice preserves the torsion `π⁻¹`
coefficient family. -/
theorem torsionPiInverseImage_inverseImage_mem
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    {ℱ : Sheaf ((S.overGrothendieckTopology @Etale).over Y) AddCommGrpCat.{u + 1}}
    (hℱ : torsionPiInverseImage Y ℱ) :
    torsionPiInverseImage X
      (((S.overGrothendieckTopology @Etale).overMapPullback AddCommGrpCat.{u + 1} f).obj
        ℱ) := sorry

/-- A torsion `π⁻¹` coefficient sheaf on the étale slice is a sheaf for the ph
topology. -/
theorem torsionPiInverseImage_isSheafPh {S : Scheme.{u}} {X : Over S}
    {ℱ : Sheaf ((S.overGrothendieckTopology @Etale).over X) AddCommGrpCat.{u + 1}}
    (hℱ : torsionPiInverseImage X ℱ) :
    Presheaf.IsSheaf ((Scheme.bigPhSite S).over X) ℱ.1 := sorry

/-- Higher direct images along proper slice morphisms preserve the torsion `π⁻¹`
coefficient family. -/
theorem torsionPiInverseImage_higherDirectImage_mem
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) (hf : properOver S f) (n : ℕ)
    {ℱ : Sheaf ((S.overGrothendieckTopology @Etale).over X) AddCommGrpCat.{u + 1}}
    (hℱ : torsionPiInverseImage X ℱ) :
    torsionPiInverseImage Y
      ((((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
          ((S.overGrothendieckTopology @Etale).over X)
          ((S.overGrothendieckTopology @Etale).over Y)).rightDerived n).obj ℱ) :=
  sorry

/-- Covering refinement from a ph covering of a slice object to an étale covering
refined by proper morphisms. -/
theorem tau_covering_refinement {S : Scheme.{u}} {U : Over S} {ι : Type i}
    (cover : ι → Over U)
    (hcover : ((Scheme.bigPhSite S).over U).CoversTop cover) :
    ∃ (J : Type (max (u + 1) i)) (V : J → Over U),
      ((S.overGrothendieckTopology @Etale).over U).CoversTop V ∧
        ∃ (W : J → Over S) (f : ∀ idx, W idx ⟶ (V idx).left),
          ∀ idx,
            properOver S (f idx) ∧
              Sieve.generate (Presieve.singleton (f idx)) ∈
                  Scheme.bigPhSite S (V idx).left ∧
                ∃ (Kidx : Type (max (u + 1) i)) (Wcover : Kidx → Over (W idx)),
                  ((S.overGrothendieckTopology @Etale).over (W idx)).CoversTop
                      Wcover ∧
                    ∀ kj : Kidx,
                      ∃ i0 : ι,
                        Nonempty
                          ((Over.mk ((Wcover kj).hom ≫ f idx ≫ (V idx).hom)) ⟶
                            cover i0) := sorry

/-- The ph/étale comparison on `Over S`, with proper morphisms and torsion `π⁻¹`
coefficients, satisfies the conditions of `TopologyComparison.Situation`. -/
instance situation (S : Scheme.{u}) :
    TopologyComparison.Situation.{u + 1, u, i, max (u + 1) i, max (u + 1) i} (Scheme.bigPhSite S)
      (S.overGrothendieckTopology @Etale) (properOver S)
      (fun X ↦ torsionPiInverseImage X) := sorry

end AlgebraicGeometry.Scheme.PhComparison

end

end
