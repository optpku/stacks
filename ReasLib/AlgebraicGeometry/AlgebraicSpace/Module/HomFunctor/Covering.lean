/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HomFunctor.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf

/-!
# Descent of module morphisms along fppf coverings

Restriction to a covering and refinements of its pairwise overlaps gives a
Čech parallel pair. For fppf coverings, its equalizer consists of the global
module morphisms on each test scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The canonical structure morphism `X_ijk ⟶ X` along `pr₀`. -/
def tripleToX {ι : Type v} {Xi : ι → AlgebraicSpace S} (fi : (i : ι) → Xi i ⟶ X)
    {κ : ι → ι → Type w} {Xijk : (i j : ι) → κ i j → AlgebraicSpace S}
    (g : (i j : ι) → (k : κ i j) → Xijk i j k ⟶ Limits.pullback (fi i) (fi j))
    (i j : ι) (k : κ i j) : Xijk i j k ⟶ X :=
  g i j k ≫ Limits.pullback.fst (fi i) (fi j) ≫ fi i

/-- The two composites `X_ijk ⟶ X_i ×_X X_j ⟶ X` agree. -/
private theorem tripleToX_snd_eq {ι : Type v} {Xi : ι → AlgebraicSpace S}
    (fi : (i : ι) → Xi i ⟶ X) {κ : ι → ι → Type w}
    {Xijk : (i j : ι) → κ i j → AlgebraicSpace S}
    (g : (i j : ι) → (k : κ i j) → Xijk i j k ⟶ Limits.pullback (fi i) (fi j))
    (i j : ι) (k : κ i j) :
    g i j k ≫ Limits.pullback.snd (fi i) (fi j) ≫ fi j =
      tripleToX fi g i j k :=
  (Category.assoc (g i j k) (Limits.pullback.snd (fi i) (fi j)) (fi j)).trans
    ((congrArg (fun p ↦ g i j k ≫ p)
        (Limits.pullback.condition :
            Limits.pullback.fst (fi i) (fi j) ≫ fi i =
              Limits.pullback.snd (fi i) (fi j) ≫ fi j).symm).trans
      (Category.assoc (g i j k) (Limits.pullback.fst (fi i) (fi j)) (fi i)).symm)

/-- Pullback of `F_i` along `X_ijk ⟶ X_i` as pullback of `F` along `tripleToX`. -/
def triplePullbackFstIso {ι : Type v} {Xi : ι → AlgebraicSpace S}
    (fi : (i : ι) → Xi i ⟶ X) {κ : ι → ι → Type w}
    {Xijk : (i j : ι) → κ i j → AlgebraicSpace S}
    (g : (i j : ι) → (k : κ i j) → Xijk i j k ⟶ Limits.pullback (fi i) (fi j))
    (F : X.Modules) (i j : ι) (k : κ i j) :
    (pullback (g i j k ≫ Limits.pullback.fst (fi i) (fi j))).obj
        ((pullback (fi i)).obj F) ≅
      (pullback (tripleToX fi g i j k)).obj F :=
  (pullbackCompIso (g i j k ≫ Limits.pullback.fst (fi i) (fi j)) (fi i)).app F

/-- Pullback of `F_j` along `X_ijk ⟶ X_j` as pullback of `F` along `tripleToX`. -/
def triplePullbackSndIso {ι : Type v} {Xi : ι → AlgebraicSpace S}
    (fi : (i : ι) → Xi i ⟶ X) {κ : ι → ι → Type w}
    {Xijk : (i j : ι) → κ i j → AlgebraicSpace S}
    (g : (i j : ι) → (k : κ i j) → Xijk i j k ⟶ Limits.pullback (fi i) (fi j))
    (F : X.Modules) (i j : ι) (k : κ i j) :
    (pullback (g i j k ≫ Limits.pullback.snd (fi i) (fi j))).obj
        ((pullback (fi j)).obj F) ≅
      (pullback (tripleToX fi g i j k)).obj F :=
  (pullbackCompIso (g i j k ≫ Limits.pullback.snd (fi i) (fi j)) (fi j)).app F ≪≫
    (pullbackCongr (by exact tripleToX_snd_eq fi g i j k)).app F

/-- The first arrow of the Čech diagram, sending a map `F_T ⟶ G_T` to the family
of restrictions `F_{i,T} ⟶ G_{i,T}`. -/
def coveringHom (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] {ι : Type v} {Xi : ι → AlgebraicSpace S}
    (fi : (i : ι) → Xi i ⟶ X) (σ : SchemeOver B)
    (u : (homFunctor f F G).obj (op σ)) (i : ι) :
    (homFunctor (fi i ≫ f) ((pullback (fi i)).obj F)
      ((pullback (fi i)).obj G)).obj (op σ) :=
  restrictHomAlong f F G (fi i) σ u

/-- `coveringHom` is restriction along each `X_i ⟶ X`. -/
theorem coveringHom_apply (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] {ι : Type v} {Xi : ι → AlgebraicSpace S}
    (fi : (i : ι) → Xi i ⟶ X) (σ : SchemeOver B)
    (u : (homFunctor f F G).obj (op σ)) (i : ι) :
    coveringHom f F G fi σ u i = restrictHomAlong f F G (fi i) σ u :=
  sorry

/-- The parallel arrow `pr₀^*`, restricting each `F_{i,T} ⟶ G_{i,T}` along
`X_ijk ⟶ X_i`. -/
def coveringPrFst (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] {ι : Type v} {Xi : ι → AlgebraicSpace S}
    (fi : (i : ι) → Xi i ⟶ X) {κ : ι → ι → Type w}
    {Xijk : (i j : ι) → κ i j → AlgebraicSpace S}
    (g : (i j : ι) → (k : κ i j) → Xijk i j k ⟶ Limits.pullback (fi i) (fi j))
    (σ : SchemeOver B)
    (s : (i : ι) →
      (homFunctor (fi i ≫ f) ((pullback (fi i)).obj F)
        ((pullback (fi i)).obj G)).obj (op σ))
    (i j : ι) (k : κ i j) :
    (homFunctor (tripleToX fi g i j k ≫ f)
      ((pullback (tripleToX fi g i j k)).obj F)
      ((pullback (tripleToX fi g i j k)).obj G)).obj (op σ) :=
  CategoryTheory.Iso.homCongr
    ((pullback (baseChangeProj (tripleToX fi g i j k ≫ f) σ.hom)).mapIso
      (triplePullbackFstIso fi g F i j k))
    ((pullback (baseChangeProj (tripleToX fi g i j k ≫ f) σ.hom)).mapIso
      (triplePullbackFstIso fi g G i j k))
    (homCast
      (Category.assoc (g i j k ≫ Limits.pullback.fst (fi i) (fi j)) (fi i) f).symm
      σ
      ((pullback (g i j k ≫ Limits.pullback.fst (fi i) (fi j))).obj
        ((pullback (fi i)).obj F))
      ((pullback (g i j k ≫ Limits.pullback.fst (fi i) (fi j))).obj
        ((pullback (fi i)).obj G))
      (restrictHomAlong (fi i ≫ f) ((pullback (fi i)).obj F)
        ((pullback (fi i)).obj G)
        (g i j k ≫ Limits.pullback.fst (fi i) (fi j)) σ (s i)))

/-- `coveringPrFst` is restriction along `X_ijk ⟶ X_i`, transported to
`tripleToX`. -/
theorem coveringPrFst_apply (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] {ι : Type v} {Xi : ι → AlgebraicSpace S}
    (fi : (i : ι) → Xi i ⟶ X) {κ : ι → ι → Type w}
    {Xijk : (i j : ι) → κ i j → AlgebraicSpace S}
    (g : (i j : ι) → (k : κ i j) → Xijk i j k ⟶ Limits.pullback (fi i) (fi j))
    (σ : SchemeOver B)
    (s : (i : ι) →
      (homFunctor (fi i ≫ f) ((pullback (fi i)).obj F)
        ((pullback (fi i)).obj G)).obj (op σ))
    (i j : ι) (k : κ i j) :
    coveringPrFst f F G fi g σ s i j k =
      CategoryTheory.Iso.homCongr
        ((pullback (baseChangeProj (tripleToX fi g i j k ≫ f) σ.hom)).mapIso
          (triplePullbackFstIso fi g F i j k))
        ((pullback (baseChangeProj (tripleToX fi g i j k ≫ f) σ.hom)).mapIso
          (triplePullbackFstIso fi g G i j k))
        (homCast
          (Category.assoc
              (g i j k ≫ Limits.pullback.fst (fi i) (fi j)) (fi i) f).symm
          σ
          ((pullback (g i j k ≫ Limits.pullback.fst (fi i) (fi j))).obj
            ((pullback (fi i)).obj F))
          ((pullback (g i j k ≫ Limits.pullback.fst (fi i) (fi j))).obj
            ((pullback (fi i)).obj G))
          (restrictHomAlong (fi i ≫ f) ((pullback (fi i)).obj F)
            ((pullback (fi i)).obj G)
            (g i j k ≫ Limits.pullback.fst (fi i) (fi j)) σ (s i))) :=
  sorry

/-- The parallel arrow `pr₁^*`, restricting each `F_{j,T} ⟶ G_{j,T}` along
`X_ijk ⟶ X_j`. -/
def coveringPrSnd (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] {ι : Type v} {Xi : ι → AlgebraicSpace S}
    (fi : (i : ι) → Xi i ⟶ X) {κ : ι → ι → Type w}
    {Xijk : (i j : ι) → κ i j → AlgebraicSpace S}
    (g : (i j : ι) → (k : κ i j) → Xijk i j k ⟶ Limits.pullback (fi i) (fi j))
    (σ : SchemeOver B)
    (s : (i : ι) →
      (homFunctor (fi i ≫ f) ((pullback (fi i)).obj F)
        ((pullback (fi i)).obj G)).obj (op σ))
    (i j : ι) (k : κ i j) :
    (homFunctor (tripleToX fi g i j k ≫ f)
      ((pullback (tripleToX fi g i j k)).obj F)
      ((pullback (tripleToX fi g i j k)).obj G)).obj (op σ) :=
  CategoryTheory.Iso.homCongr
    ((pullback (baseChangeProj (tripleToX fi g i j k ≫ f) σ.hom)).mapIso
      (triplePullbackSndIso fi g F i j k))
    ((pullback (baseChangeProj (tripleToX fi g i j k ≫ f) σ.hom)).mapIso
      (triplePullbackSndIso fi g G i j k))
    (homCast
      ((Category.assoc
            (g i j k ≫ Limits.pullback.snd (fi i) (fi j)) (fi j) f).symm.trans
        (congrArg (fun p ↦ p ≫ f) (by exact tripleToX_snd_eq fi g i j k)))
      σ
      ((pullback (g i j k ≫ Limits.pullback.snd (fi i) (fi j))).obj
        ((pullback (fi j)).obj F))
      ((pullback (g i j k ≫ Limits.pullback.snd (fi i) (fi j))).obj
        ((pullback (fi j)).obj G))
      (restrictHomAlong (fi j ≫ f) ((pullback (fi j)).obj F)
        ((pullback (fi j)).obj G)
        (g i j k ≫ Limits.pullback.snd (fi i) (fi j)) σ (s j)))

/-- `coveringPrSnd` is restriction along `X_ijk ⟶ X_j`, transported to
`tripleToX`. -/
theorem coveringPrSnd_apply (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] {ι : Type v} {Xi : ι → AlgebraicSpace S}
    (fi : (i : ι) → Xi i ⟶ X) {κ : ι → ι → Type w}
    {Xijk : (i j : ι) → κ i j → AlgebraicSpace S}
    (g : (i j : ι) → (k : κ i j) → Xijk i j k ⟶ Limits.pullback (fi i) (fi j))
    (σ : SchemeOver B)
    (s : (i : ι) →
      (homFunctor (fi i ≫ f) ((pullback (fi i)).obj F)
        ((pullback (fi i)).obj G)).obj (op σ))
    (i j : ι) (k : κ i j) :
    coveringPrSnd f F G fi g σ s i j k =
      CategoryTheory.Iso.homCongr
        ((pullback (baseChangeProj (tripleToX fi g i j k ≫ f) σ.hom)).mapIso
          (triplePullbackSndIso fi g F i j k))
        ((pullback (baseChangeProj (tripleToX fi g i j k ≫ f) σ.hom)).mapIso
          (triplePullbackSndIso fi g G i j k))
        (homCast
          ((Category.assoc
                (g i j k ≫ Limits.pullback.snd (fi i) (fi j)) (fi j) f).symm.trans
            (congrArg (fun p ↦ p ≫ f) (by exact tripleToX_snd_eq fi g i j k)))
          σ
          ((pullback (g i j k ≫ Limits.pullback.snd (fi i) (fi j))).obj
            ((pullback (fi j)).obj F))
          ((pullback (g i j k ≫ Limits.pullback.snd (fi i) (fi j))).obj
            ((pullback (fi j)).obj G))
          (restrictHomAlong (fi j ≫ f) ((pullback (fi j)).obj F)
            ((pullback (fi j)).obj G)
            (g i j k ≫ Limits.pullback.snd (fi i) (fi j)) σ (s j))) :=
  sorry

/-- The two Čech restrictions of a global map `F_T ⟶ G_T` agree. -/
theorem covering_equalizes (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent]
    [G.IsQuasicoherent] {ι : Type v} {Xi : ι → AlgebraicSpace S}
    (fi : (i : ι) → Xi i ⟶ X) {κ : ι → ι → Type w}
    {Xijk : (i j : ι) → κ i j → AlgebraicSpace S}
    (g : (i j : ι) → (k : κ i j) → Xijk i j k ⟶ Limits.pullback (fi i) (fi j))
    (σ : SchemeOver B) (u : (homFunctor f F G).obj (op σ)) :
    coveringPrFst f F G fi g σ (coveringHom f F G fi σ u) =
      coveringPrSnd f F G fi g σ (coveringHom f F G fi σ u) :=
  sorry

/-- An fppf covering `{X_i ⟶ X}` together
with fppf coverings `{X_ijk ⟶ X_i ×_X X_j}` presents `Hom(F, G)(T)` as the
equalizer of the two restrictions
`∏_i Hom(F_i, G_i)(T) ⇉ ∏_{i,j,k} Hom(F_ijk, G_ijk)(T)`
for every scheme `T` over `B`. -/
theorem homFunctor_covering_equalizer {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {ι : Type v} {Xi : ι → AlgebraicSpace S} (fi : (i : ι) → Xi i ⟶ X)
    [FppfCovering Xi fi] {κ : ι → ι → Type w}
    {Xijk : (i j : ι) → κ i j → AlgebraicSpace S}
    (g : (i j : ι) → (k : κ i j) → Xijk i j k ⟶ Limits.pullback (fi i) (fi j))
    [∀ i j, FppfCovering (Xijk i j) (g i j)] (σ : SchemeOver B) :
    (∀ u, coveringPrFst f F G fi g σ (coveringHom f F G fi σ u) =
      coveringPrSnd f F G fi g σ (coveringHom f F G fi σ u)) ∧
    (∀ s : (i : ι) →
      (homFunctor (fi i ≫ f) ((pullback (fi i)).obj F)
        ((pullback (fi i)).obj G)).obj (op σ),
      coveringPrFst f F G fi g σ s = coveringPrSnd f F G fi g σ s →
        ∃! u, coveringHom f F G fi σ u = s) :=
  sorry

/-- The restriction map `Hom(F, G)(T) ⟶ ∏_i Hom(F_i, G_i)(T)` is injective. -/
theorem homFunctor_covering_injective {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {ι : Type v} {Xi : ι → AlgebraicSpace S} (fi : (i : ι) → Xi i ⟶ X)
    [FppfCovering Xi fi] {κ : ι → ι → Type w}
    {Xijk : (i j : ι) → κ i j → AlgebraicSpace S}
    (g : (i j : ι) → (k : κ i j) → Xijk i j k ⟶ Limits.pullback (fi i) (fi j))
    [∀ i j, FppfCovering (Xijk i j) (g i j)] (σ : SchemeOver B) :
    Function.Injective (coveringHom f F G fi σ) :=
  sorry

/-- A family in `∏_i Hom(F_i, G_i)(T)` comes from `Hom(F, G)(T)` if and only if
it is equalized by `pr₀^*` and `pr₁^*`. -/
theorem coveringHom_eq_iff {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    {ι : Type v} {Xi : ι → AlgebraicSpace S} (fi : (i : ι) → Xi i ⟶ X)
    [FppfCovering Xi fi] {κ : ι → ι → Type w}
    {Xijk : (i j : ι) → κ i j → AlgebraicSpace S}
    (g : (i j : ι) → (k : κ i j) → Xijk i j k ⟶ Limits.pullback (fi i) (fi j))
    [∀ i j, FppfCovering (Xijk i j) (g i j)] (σ : SchemeOver B)
    (s : (i : ι) →
      (homFunctor (fi i ≫ f) ((pullback (fi i)).obj F)
        ((pullback (fi i)).obj G)).obj (op σ)) :
    (∃ u, coveringHom f F G fi σ u = s) ↔
      coveringPrFst f F G fi g σ s = coveringPrSnd f F G fi g σ s :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
