/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.BaseChange
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Fpqc descent of quotient points

Restriction to an fpqc family, together with fpqc refinements of its pairwise overlaps,
presents the quotient functor and its finite-presentation subfunctor as equalizers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The composite `X_ijk ⟶ X` of an overlap member with `pr₀` and `X_i ⟶ X`. -/
def tripleToX {I : Type v} (family : I → Over X) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (i j : I) (k : K i j) : (overlap i j k).left ⟶ X :=
  (overlap i j k).hom ≫ pullback.fst (family i).hom (family j).hom ≫
    (family i).hom

/-- The first projection composite of an overlap member recovers `tripleToX`. -/
theorem tripleToX_fst_eq {I : Type v} (family : I → Over X) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (i j : I) (k : K i j) :
    ((overlap i j k).hom ≫ pullback.fst (family i).hom (family j).hom) ≫
        (family i).hom =
      tripleToX family overlap i j k :=
  Category.assoc (overlap i j k).hom
    (pullback.fst (family i).hom (family j).hom) (family i).hom

/-- The second projection composite of an overlap member recovers `tripleToX`. -/
theorem tripleToX_snd_eq {I : Type v} (family : I → Over X) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (i j : I) (k : K i j) :
    ((overlap i j k).hom ≫ pullback.snd (family i).hom (family j).hom) ≫
        (family j).hom =
      tripleToX family overlap i j k :=
  (Category.assoc (overlap i j k).hom
      (pullback.snd (family i).hom (family j).hom) (family j).hom).trans
    (congrArg ((overlap i j k).hom ≫ ·)
      (pullback.condition :
          pullback.fst (family i).hom (family j).hom ≫ (family i).hom =
            pullback.snd (family i).hom (family j).hom ≫ (family j).hom).symm)

/-- Associativity identifying restriction along `X_ijk ⟶ X_i` with `tripleToX`. -/
theorem tripleToX_fst_comp_eq (f : X ⟶ B) {I : Type v} (family : I → Over X)
    {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (i j : I) (k : K i j) :
    ((overlap i j k).hom ≫ pullback.fst (family i).hom (family j).hom) ≫
        ((family i).hom ≫ f) =
      tripleToX family overlap i j k ≫ f :=
  ((Category.assoc
        ((overlap i j k).hom ≫ pullback.fst (family i).hom (family j).hom)
        (family i).hom f).symm).trans
    (congrArg (· ≫ f) (tripleToX_fst_eq family overlap i j k))

/-- Associativity identifying restriction along `X_ijk ⟶ X_j` with `tripleToX`. -/
theorem tripleToX_snd_comp_eq (f : X ⟶ B) {I : Type v} (family : I → Over X)
    {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (i j : I) (k : K i j) :
    ((overlap i j k).hom ≫ pullback.snd (family i).hom (family j).hom) ≫
        ((family j).hom ≫ f) =
      tripleToX family overlap i j k ≫ f :=
  ((Category.assoc
        ((overlap i j k).hom ≫ pullback.snd (family i).hom (family j).hom)
        (family j).hom f).symm).trans
    (congrArg (· ≫ f) (tripleToX_snd_eq family overlap i j k))

/-- Pullback of `F_i` along `X_ijk ⟶ X_i` as pullback of `F` along `tripleToX`. -/
def overlapPullbackFstIso (F : X.Modules) {I : Type v} (family : I → Over X)
    {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (i j : I) (k : K i j) :
    (Modules.pullback
        ((overlap i j k).hom ≫ pullback.fst (family i).hom (family j).hom)).obj
      ((Modules.pullback (family i).hom).obj F) ≅
      (Modules.pullback (tripleToX family overlap i j k)).obj F :=
  (Modules.pullbackCompIso
      ((overlap i j k).hom ≫ pullback.fst (family i).hom (family j).hom)
      (family i).hom).app F ≪≫
    eqToIso (congrArg (fun ψ ↦ (Modules.pullback ψ).obj F)
      (tripleToX_fst_eq family overlap i j k))

/-- Pullback of `F_j` along `X_ijk ⟶ X_j` as pullback of `F` along `tripleToX`. -/
def overlapPullbackSndIso (F : X.Modules) {I : Type v} (family : I → Over X)
    {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (i j : I) (k : K i j) :
    (Modules.pullback
        ((overlap i j k).hom ≫ pullback.snd (family i).hom (family j).hom)).obj
      ((Modules.pullback (family j).hom).obj F) ≅
      (Modules.pullback (tripleToX family overlap i j k)).obj F :=
  (Modules.pullbackCompIso
      ((overlap i j k).hom ≫ pullback.snd (family i).hom (family j).hom)
      (family j).hom).app F ≪≫
    eqToIso (congrArg (fun ψ ↦ (Modules.pullback ψ).obj F)
      (tripleToX_snd_eq family overlap i j k))

/-- The quotient functor of the pullback of `F` to a covering member `X_i`. -/
abbrev memberFunctor (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {I : Type v} (family : I → Over X) (i : I) :=
  functor ((family i).hom ≫ f) ((Modules.pullback (family i).hom).obj F)

/-- The quotient functor of the pullback of `F` to an overlap member `X_ijk`. -/
abbrev overlapFunctor (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {I : Type v} (family : I → Over X) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (i j : I) (k : K i j) :=
  functor (tripleToX family overlap i j k ≫ f)
    ((Modules.pullback (tripleToX family overlap i j k)).obj F)

/-- The finitely presented quotient functor of the pullback of `F` to a covering
member `X_i`. -/
abbrev fpMemberFunctor (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {I : Type v} (family : I → Over X) (i : I) :=
  fpFunctor ((family i).hom ≫ f) ((Modules.pullback (family i).hom).obj F)

/-- The finitely presented quotient functor of the pullback of `F` to an overlap
member `X_ijk`. -/
abbrev fpOverlapFunctor (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {I : Type v} (family : I → Over X) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (i j : I) (k : K i j) :=
  fpFunctor (tripleToX family overlap i j k ≫ f)
    ((Modules.pullback (tripleToX family overlap i j k)).obj F)

/-- The first arrow of the Čech diagram, sending a class in `Q_{F/X/B}(T)` to the
family of restrictions in `∏_i Q_{F_i/X_i/B}(T)`. -/
def coveringHom (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    (family : I → Over X) (hflat : ∀ i, Flat (family i).hom) (σ : SchemeOver B)
    (u : (functor f F).obj (op σ)) (i : I) :
    (memberFunctor f F family i).obj (op σ) :=
  restrictAlong f F (family i).hom (hflat i) σ u

/-- `coveringHom` is restriction along each `X_i ⟶ X`. -/
theorem coveringHom_apply (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {I : Type v} (family : I → Over X) (hflat : ∀ i, Flat (family i).hom) (σ : SchemeOver B)
    (u : (functor f F).obj (op σ)) (i : I) :
    coveringHom f F family hflat σ u i = restrictAlong f F (family i).hom (hflat i) σ u :=
  rfl

/-- The parallel arrow `pr₀^*`, restricting each class on `X_i` along
`X_ijk ⟶ X_i`. -/
def coveringPrFst (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    (family : I → Over X) (hflat : ∀ i, Flat (family i).hom) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (hoverlapFlat : ∀ i j k, Flat (overlap i j k).hom)
    (σ : SchemeOver B)
    (s : (i : I) → (memberFunctor f F family i).obj (op σ)) (i j : I)
    (k : K i j) : (overlapFunctor f F family overlap i j k).obj (op σ) :=
  functorCongr (tripleToX_fst_comp_eq f family overlap i j k)
    (overlapPullbackFstIso F family overlap i j k) σ
    (restrictAlong ((family i).hom ≫ f)
      ((Modules.pullback (family i).hom).obj F)
      ((overlap i j k).hom ≫ pullback.fst (family i).hom (family j).hom)
          (@flat_comp S _ _ _ (overlap i j k).hom
            (pullback.fst (family i).hom (family j).hom)
            (hoverlapFlat i j k)
            (CategoryTheory.MorphismProperty.pullback_fst
              (family i).hom (family j).hom (hflat j))) σ
      (s i))

/-- `coveringPrFst` is restriction along `X_ijk ⟶ X_i`, transported to
`tripleToX`. -/
theorem coveringPrFst_apply (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {I : Type v} (family : I → Over X) (hflat : ∀ i, Flat (family i).hom) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (hoverlapFlat : ∀ i j k, Flat (overlap i j k).hom)
    (σ : SchemeOver B)
    (s : (i : I) → (memberFunctor f F family i).obj (op σ)) (i j : I)
    (k : K i j) :
    coveringPrFst f F family hflat overlap hoverlapFlat σ s i j k =
      functorCongr (tripleToX_fst_comp_eq f family overlap i j k)
        (overlapPullbackFstIso F family overlap i j k) σ
        (restrictAlong ((family i).hom ≫ f)
          ((Modules.pullback (family i).hom).obj F)
          ((overlap i j k).hom ≫ pullback.fst (family i).hom (family j).hom)
          (@flat_comp S _ _ _ (overlap i j k).hom
            (pullback.fst (family i).hom (family j).hom)
            (hoverlapFlat i j k)
            (CategoryTheory.MorphismProperty.pullback_fst
              (family i).hom (family j).hom (hflat j))) σ
          (s i)) :=
  rfl

/-- The parallel arrow `pr₁^*`, restricting each class on `X_j` along
`X_ijk ⟶ X_j`. -/
def coveringPrSnd (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    (family : I → Over X) (hflat : ∀ i, Flat (family i).hom) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (hoverlapFlat : ∀ i j k, Flat (overlap i j k).hom)
    (σ : SchemeOver B)
    (s : (i : I) → (memberFunctor f F family i).obj (op σ)) (i j : I)
    (k : K i j) : (overlapFunctor f F family overlap i j k).obj (op σ) :=
  functorCongr (tripleToX_snd_comp_eq f family overlap i j k)
    (overlapPullbackSndIso F family overlap i j k) σ
    (restrictAlong ((family j).hom ≫ f)
      ((Modules.pullback (family j).hom).obj F)
      ((overlap i j k).hom ≫ pullback.snd (family i).hom (family j).hom)
          (@flat_comp S _ _ _ (overlap i j k).hom
            (pullback.snd (family i).hom (family j).hom)
            (hoverlapFlat i j k)
            (CategoryTheory.MorphismProperty.pullback_snd
              (family i).hom (family j).hom (hflat i))) σ
      (s j))

/-- `coveringPrSnd` is restriction along `X_ijk ⟶ X_j`, transported to
`tripleToX`. -/
theorem coveringPrSnd_apply (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {I : Type v} (family : I → Over X) (hflat : ∀ i, Flat (family i).hom) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (hoverlapFlat : ∀ i j k, Flat (overlap i j k).hom)
    (σ : SchemeOver B)
    (s : (i : I) → (memberFunctor f F family i).obj (op σ)) (i j : I)
    (k : K i j) :
    coveringPrSnd f F family hflat overlap hoverlapFlat σ s i j k =
      functorCongr (tripleToX_snd_comp_eq f family overlap i j k)
        (overlapPullbackSndIso F family overlap i j k) σ
        (restrictAlong ((family j).hom ≫ f)
          ((Modules.pullback (family j).hom).obj F)
          ((overlap i j k).hom ≫ pullback.snd (family i).hom (family j).hom)
          (@flat_comp S _ _ _ (overlap i j k).hom
            (pullback.snd (family i).hom (family j).hom)
            (hoverlapFlat i j k)
            (CategoryTheory.MorphismProperty.pullback_snd
              (family i).hom (family j).hom (hflat i))) σ
          (s j)) :=
  rfl

/-- The two Čech restrictions of a global class in `Q_{F/X/B}(T)` agree. -/
theorem covering_equalizes (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {I : Type v} (family : I → Over X) (hflat : ∀ i, Flat (family i).hom) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (hoverlapFlat : ∀ i j k, Flat (overlap i j k).hom)
    (σ : SchemeOver B) (u : (functor f F).obj (op σ)) :
    coveringPrFst f F family hflat overlap hoverlapFlat σ (coveringHom f F family hflat σ u) =
      coveringPrSnd f F family hflat overlap hoverlapFlat σ (coveringHom f F family hflat σ u) :=
  sorry

/-- The first arrow of the Čech diagram for `Q^{fp}_{F/X/B}`. -/
def fpCoveringHom (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    (family : I → Over X) (hflat : ∀ i, Flat (family i).hom) (σ : SchemeOver B)
    (u : (fpFunctor f F).obj (op σ)) (i : I) :
    (fpMemberFunctor f F family i).obj (op σ) :=
  fpRestrictAlong f F (family i).hom (hflat i) σ u

/-- `fpCoveringHom` is restriction along each `X_i ⟶ X`. -/
theorem fpCoveringHom_apply (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {I : Type v} (family : I → Over X) (hflat : ∀ i, Flat (family i).hom) (σ : SchemeOver B)
    (u : (fpFunctor f F).obj (op σ)) (i : I) :
    fpCoveringHom f F family hflat σ u i = fpRestrictAlong f F (family i).hom (hflat i) σ u :=
  rfl

/-- The parallel arrow `pr₀^*` for `Q^{fp}_{F/X/B}`. -/
def fpCoveringPrFst (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    (family : I → Over X) (hflat : ∀ i, Flat (family i).hom) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (hoverlapFlat : ∀ i j k, Flat (overlap i j k).hom)
    (σ : SchemeOver B)
    (s : (i : I) → (fpMemberFunctor f F family i).obj (op σ)) (i j : I)
    (k : K i j) : (fpOverlapFunctor f F family overlap i j k).obj (op σ) :=
  fpFunctorCongr (tripleToX_fst_comp_eq f family overlap i j k)
    (overlapPullbackFstIso F family overlap i j k) σ
    (fpRestrictAlong ((family i).hom ≫ f)
      ((Modules.pullback (family i).hom).obj F)
      ((overlap i j k).hom ≫ pullback.fst (family i).hom (family j).hom)
          (@flat_comp S _ _ _ (overlap i j k).hom
            (pullback.fst (family i).hom (family j).hom)
            (hoverlapFlat i j k)
            (CategoryTheory.MorphismProperty.pullback_fst
              (family i).hom (family j).hom (hflat j))) σ
      (s i))

/-- `fpCoveringPrFst` is restriction along `X_ijk ⟶ X_i`, transported to
`tripleToX`. -/
theorem fpCoveringPrFst_apply (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {I : Type v} (family : I → Over X) (hflat : ∀ i, Flat (family i).hom) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (hoverlapFlat : ∀ i j k, Flat (overlap i j k).hom)
    (σ : SchemeOver B)
    (s : (i : I) → (fpMemberFunctor f F family i).obj (op σ)) (i j : I)
    (k : K i j) :
    fpCoveringPrFst f F family hflat overlap hoverlapFlat σ s i j k =
      fpFunctorCongr (tripleToX_fst_comp_eq f family overlap i j k)
        (overlapPullbackFstIso F family overlap i j k) σ
        (fpRestrictAlong ((family i).hom ≫ f)
          ((Modules.pullback (family i).hom).obj F)
          ((overlap i j k).hom ≫ pullback.fst (family i).hom (family j).hom)
          (@flat_comp S _ _ _ (overlap i j k).hom
            (pullback.fst (family i).hom (family j).hom)
            (hoverlapFlat i j k)
            (CategoryTheory.MorphismProperty.pullback_fst
              (family i).hom (family j).hom (hflat j))) σ
          (s i)) :=
  rfl

/-- The parallel arrow `pr₁^*` for `Q^{fp}_{F/X/B}`. -/
def fpCoveringPrSnd (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    (family : I → Over X) (hflat : ∀ i, Flat (family i).hom) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (hoverlapFlat : ∀ i j k, Flat (overlap i j k).hom)
    (σ : SchemeOver B)
    (s : (i : I) → (fpMemberFunctor f F family i).obj (op σ)) (i j : I)
    (k : K i j) : (fpOverlapFunctor f F family overlap i j k).obj (op σ) :=
  fpFunctorCongr (tripleToX_snd_comp_eq f family overlap i j k)
    (overlapPullbackSndIso F family overlap i j k) σ
    (fpRestrictAlong ((family j).hom ≫ f)
      ((Modules.pullback (family j).hom).obj F)
      ((overlap i j k).hom ≫ pullback.snd (family i).hom (family j).hom)
          (@flat_comp S _ _ _ (overlap i j k).hom
            (pullback.snd (family i).hom (family j).hom)
            (hoverlapFlat i j k)
            (CategoryTheory.MorphismProperty.pullback_snd
              (family i).hom (family j).hom (hflat i))) σ
      (s j))

/-- `fpCoveringPrSnd` is restriction along `X_ijk ⟶ X_j`, transported to
`tripleToX`. -/
theorem fpCoveringPrSnd_apply (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {I : Type v} (family : I → Over X) (hflat : ∀ i, Flat (family i).hom) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (hoverlapFlat : ∀ i j k, Flat (overlap i j k).hom)
    (σ : SchemeOver B)
    (s : (i : I) → (fpMemberFunctor f F family i).obj (op σ)) (i j : I)
    (k : K i j) :
    fpCoveringPrSnd f F family hflat overlap hoverlapFlat σ s i j k =
      fpFunctorCongr (tripleToX_snd_comp_eq f family overlap i j k)
        (overlapPullbackSndIso F family overlap i j k) σ
        (fpRestrictAlong ((family j).hom ≫ f)
          ((Modules.pullback (family j).hom).obj F)
          ((overlap i j k).hom ≫ pullback.snd (family i).hom (family j).hom)
          (@flat_comp S _ _ _ (overlap i j k).hom
            (pullback.snd (family i).hom (family j).hom)
            (hoverlapFlat i j k)
            (CategoryTheory.MorphismProperty.pullback_snd
              (family i).hom (family j).hom (hflat i))) σ
          (s j)) :=
  rfl

/-- The two Čech restrictions of a global class in `Q^{fp}_{F/X/B}(T)` agree. -/
theorem fp_covering_equalizes (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {I : Type v} (family : I → Over X) (hflat : ∀ i, Flat (family i).hom) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (hoverlapFlat : ∀ i j k, Flat (overlap i j k).hom)
    (σ : SchemeOver B) (u : (fpFunctor f F).obj (op σ)) :
    fpCoveringPrFst f F family hflat overlap hoverlapFlat σ (fpCoveringHom f F family hflat σ u) =
      fpCoveringPrSnd f F family hflat overlap hoverlapFlat σ (fpCoveringHom f F family hflat σ u) :=
  sorry

/-- An fpqc covering `{X_i ⟶ X}` together
with fpqc coverings `{X_ijk ⟶ X_i ×_X X_j}` presents `Q_{F/X/B}(T)` as the
equalizer of the two restrictions
`∏_i Q_{F_i/X_i/B}(T) ⇉ ∏_{i,j,k} Q_{F_ijk/X_ijk/B}(T)`
for every scheme `T` over `B`. -/
@[stacks 08IV]
theorem functor_covering_equalizer {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    {family : I → Over X} (hfamily : FpqcCovering family) {K : I → I → Type w}
    {overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom)}
    (hoverlap : ∀ i j, FpqcCovering (overlap i j)) (σ : SchemeOver B)
    (s : (i : I) → (memberFunctor f F family i).obj (op σ))
    (hs : coveringPrFst f F family hfamily.flat overlap (fun i j ↦ (hoverlap i j).flat) σ s =
      coveringPrSnd f F family hfamily.flat overlap (fun i j ↦ (hoverlap i j).flat) σ s) :
    ∃! u, coveringHom f F family hfamily.flat σ u = s :=
  sorry

/-- The restriction map `Q_{F/X/B}(T) ⟶ ∏_i Q_{F_i/X_i/B}(T)` is injective. -/
theorem coveringHom_injective {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    {family : I → Over X} (hfamily : FpqcCovering family) {K : I → I → Type w}
    {overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom)}
    (hoverlap : ∀ i j, FpqcCovering (overlap i j)) (σ : SchemeOver B) :
    Function.Injective (coveringHom f F family hfamily.flat σ) :=
  sorry

/-- A family in `∏_i Q_{F_i/X_i/B}(T)` comes from `Q_{F/X/B}(T)` if and only if
it is equalized by `pr₀^*` and `pr₁^*`. -/
theorem coveringHom_eq_iff {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    {family : I → Over X} (hfamily : FpqcCovering family) {K : I → I → Type w}
    {overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom)}
    (hoverlap : ∀ i j, FpqcCovering (overlap i j)) (σ : SchemeOver B)
    (s : (i : I) → (memberFunctor f F family i).obj (op σ)) :
    (∃ u, coveringHom f F family hfamily.flat σ u = s) ↔
      coveringPrFst f F family hfamily.flat overlap (fun i j ↦ (hoverlap i j).flat) σ s =
        coveringPrSnd f F family hfamily.flat overlap (fun i j ↦ (hoverlap i j).flat) σ s :=
  sorry

/-- An fpqc covering `{X_i ⟶ X}` together
with fpqc coverings `{X_ijk ⟶ X_i ×_X X_j}` presents `Q^{fp}_{F/X/B}(T)` as the
equalizer of the two restrictions
`∏_i Q^{fp}_{F_i/X_i/B}(T) ⇉ ∏_{i,j,k} Q^{fp}_{F_ijk/X_ijk/B}(T)`
for every scheme `T` over `B`. -/
@[stacks 08IV]
theorem fpFunctor_covering_equalizer {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    {family : I → Over X} (hfamily : FpqcCovering family) {K : I → I → Type w}
    {overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom)}
    (hoverlap : ∀ i j, FpqcCovering (overlap i j)) (σ : SchemeOver B)
    (s : (i : I) → (fpMemberFunctor f F family i).obj (op σ))
    (hs : fpCoveringPrFst f F family hfamily.flat overlap (fun i j ↦ (hoverlap i j).flat) σ s =
      fpCoveringPrSnd f F family hfamily.flat overlap (fun i j ↦ (hoverlap i j).flat) σ s) :
    ∃! u, fpCoveringHom f F family hfamily.flat σ u = s :=
  sorry

/-- The restriction map `Q^{fp}_{F/X/B}(T) ⟶ ∏_i Q^{fp}_{F_i/X_i/B}(T)` is
injective. -/
theorem fpCoveringHom_injective {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    {family : I → Over X} (hfamily : FpqcCovering family) {K : I → I → Type w}
    {overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom)}
    (hoverlap : ∀ i j, FpqcCovering (overlap i j)) (σ : SchemeOver B) :
    Function.Injective (fpCoveringHom f F family hfamily.flat σ) :=
  sorry

/-- A family in `∏_i Q^{fp}_{F_i/X_i/B}(T)` comes from `Q^{fp}_{F/X/B}(T)` if and
only if it is equalized by `pr₀^*` and `pr₁^*`. -/
theorem fpCoveringHom_eq_iff {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    {family : I → Over X} (hfamily : FpqcCovering family) {K : I → I → Type w}
    {overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom)}
    (hoverlap : ∀ i j, FpqcCovering (overlap i j)) (σ : SchemeOver B)
    (s : (i : I) → (fpMemberFunctor f F family i).obj (op σ)) :
    (∃ u, fpCoveringHom f F family hfamily.flat σ u = s) ↔
      fpCoveringPrFst f F family hfamily.flat overlap (fun i j ↦ (hoverlap i j).flat) σ s =
        fpCoveringPrSnd f F family hfamily.flat overlap (fun i j ↦ (hoverlap i j).flat) σ s :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
