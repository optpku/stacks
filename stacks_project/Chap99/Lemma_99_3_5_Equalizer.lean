/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import stacks_project.Chap73.Definition_73_7_1_FppfCover
public import stacks_project.Chap99.«99_3_1_1»

/-!
# Restriction of Hom along a covering of the total space

Given quasi-coherent modules `F`, `G` on `X`, a morphism `φ : X' ⟶ X` over `B`
induces restriction of `𝒪_{X_T}`-module maps along `X'_T ⟶ X_T`. An fppf
covering of `X` together with coverings of the fibre products `X_i ×_X X_j`
then yields the Čech parallel pair on values of `Hom(F, G)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The pasting isomorphism `X'_T ≅ X' ×_X X_T`. -/
def restrictSpaceIso (f : X ⟶ B) {X' : AlgebraicSpace S} (φ : X' ⟶ X)
    (σ : SchemeOver B) :
    baseChangeSpace (φ ≫ f) σ.hom ≅ Limits.pullback φ (baseChangeProj f σ.hom) :=
  (pullbackRightPullbackFstIso f σ.hom φ).symm

/-- The canonical map `X'_T ⟶ X_T` induced by `φ : X' ⟶ X`. -/
def restrictSpaceMap (f : X ⟶ B) {X' : AlgebraicSpace S} (φ : X' ⟶ X)
    (σ : SchemeOver B) :
    baseChangeSpace (φ ≫ f) σ.hom ⟶ baseChangeSpace f σ.hom :=
  Limits.pullback.lift
    (baseChangeProj (φ ≫ f) σ.hom ≫ φ)
    (Limits.pullback.snd (φ ≫ f) σ.hom)
    ((Category.assoc (baseChangeProj (φ ≫ f) σ.hom) φ f).trans
      (Limits.pullback.condition :
        Limits.pullback.fst (φ ≫ f) σ.hom ≫ (φ ≫ f) =
          Limits.pullback.snd (φ ≫ f) σ.hom ≫ σ.hom))

/-- `restrictSpaceMap` is the second projection of `X' ×_X X_T` after pasting. -/
theorem restrictSpaceMap_eq_pasting (f : X ⟶ B) {X' : AlgebraicSpace S}
    (φ : X' ⟶ X) (σ : SchemeOver B) :
    restrictSpaceMap f φ σ =
      (restrictSpaceIso f φ σ).hom ≫
        Limits.pullback.snd φ (baseChangeProj f σ.hom) :=
  sorry

/-- `restrictSpaceMap` commutes with the projections to `X`. -/
def restrictSpaceMap_comp_proj (f : X ⟶ B) {X' : AlgebraicSpace S} (φ : X' ⟶ X)
    (σ : SchemeOver B) :
    restrictSpaceMap f φ σ ≫ baseChangeProj f σ.hom =
      baseChangeProj (φ ≫ f) σ.hom ≫ φ :=
  Limits.pullback.lift_fst
    (baseChangeProj (φ ≫ f) σ.hom ≫ φ)
    (Limits.pullback.snd (φ ≫ f) σ.hom)
    ((Category.assoc (baseChangeProj (φ ≫ f) σ.hom) φ f).trans
      (Limits.pullback.condition :
        Limits.pullback.fst (φ ≫ f) σ.hom ≫ (φ ≫ f) =
          Limits.pullback.snd (φ ≫ f) σ.hom ≫ σ.hom))

/-- Identification of `(φ^* F)_T` with the pullback of `F_T` along `X'_T ⟶ X_T`. -/
def restrictModuleIso (f : X ⟶ B) {X' : AlgebraicSpace S} (φ : X' ⟶ X)
    (σ : SchemeOver B) (F : X.Modules) :
    baseChangeModule (φ ≫ f) σ.hom ((pullback φ).obj F) ≅
      (pullback (restrictSpaceMap f φ σ)).obj (baseChangeModule f σ.hom F) :=
  (pullbackComp (baseChangeProj (φ ≫ f) σ.hom) φ).app F ≪≫
    (pullbackCongr (restrictSpaceMap_comp_proj f φ σ).symm).app F ≪≫
    (pullbackComp (restrictSpaceMap f φ σ) (baseChangeProj f σ.hom)).symm.app F

/-- Restriction of an `𝒪_{X_T}`-module map along a morphism `φ : X' ⟶ X` over `B`. -/
def restrictHomAlong (f : X ⟶ B) (F G : X.Modules) {X' : AlgebraicSpace S}
    (φ : X' ⟶ X) (σ : SchemeOver B)
    (u : baseChangeModule f σ.hom F ⟶ baseChangeModule f σ.hom G) :
    baseChangeModule (φ ≫ f) σ.hom ((pullback φ).obj F) ⟶
      baseChangeModule (φ ≫ f) σ.hom ((pullback φ).obj G) :=
  (restrictModuleIso f φ σ F).hom ≫
    (pullback (restrictSpaceMap f φ σ)).map u ≫ (restrictModuleIso f φ σ G).inv

/-- After the pasting identification, `restrictHomAlong` is pullback along
`restrictSpaceMap`. -/
theorem restrictHomAlong_spec (f : X ⟶ B) (F G : X.Modules)
    {X' : AlgebraicSpace S} (φ : X' ⟶ X) (σ : SchemeOver B)
    (u : baseChangeModule f σ.hom F ⟶ baseChangeModule f σ.hom G) :
    restrictHomAlong f F G φ σ u =
      (restrictModuleIso f φ σ F).hom ≫
        (pullback (restrictSpaceMap f φ σ)).map u ≫
          (restrictModuleIso f φ σ G).inv :=
  sorry

/-- Transport of a base-changed Hom along an equality of structure morphisms over `B`. -/
def homCast {X' : AlgebraicSpace S} {α β : X' ⟶ B} (h : α = β) (σ : SchemeOver B)
    (F G : X'.Modules)
    (u : baseChangeModule α σ.hom F ⟶ baseChangeModule α σ.hom G) :
    baseChangeModule β σ.hom F ⟶ baseChangeModule β σ.hom G :=
  cast (congrArg (fun γ ↦
      (baseChangeModule γ σ.hom F ⟶ baseChangeModule γ σ.hom G)) h) u

/-- Conjugation of a module morphism by a pair of isomorphisms. -/
def homCongr {Y : AlgebraicSpace S} {A A' B B' : Y.Modules} (eA : A ≅ A')
    (eB : B ≅ B') (u : A ⟶ B) : A' ⟶ B' :=
  eA.inv ≫ u ≫ eB.hom


/-- Restriction along `𝟙 X` recovers the original map after the identity
identifications of structure morphisms and module pullbacks. -/
theorem restrictHomAlong_id (f : X ⟶ B) (F G : X.Modules) (σ : SchemeOver B)
    (u : baseChangeModule f σ.hom F ⟶ baseChangeModule f σ.hom G) :
    ∃ (eF : (pullback (𝟙 X)).obj F ≅ F) (eG : (pullback (𝟙 X)).obj G ≅ G),
      homCongr
          ((pullback (baseChangeProj f σ.hom)).mapIso eF)
          ((pullback (baseChangeProj f σ.hom)).mapIso eG)
          (homCast (Category.id_comp f) σ ((pullback (𝟙 X)).obj F)
            ((pullback (𝟙 X)).obj G) (restrictHomAlong f F G (𝟙 X) σ u)) =
        u :=
  sorry

/-- Restriction along a composite `X'' ⟶ X' ⟶ X` is the composite restriction. -/
theorem restrictHomAlong_comp (f : X ⟶ B) (F G : X.Modules)
    {X' X'' : AlgebraicSpace S} (φ : X' ⟶ X) (ψ : X'' ⟶ X') (σ : SchemeOver B)
    (u : baseChangeModule f σ.hom F ⟶ baseChangeModule f σ.hom G) :
    restrictHomAlong f F G (ψ ≫ φ) σ u =
      homCongr
        ((pullback (baseChangeProj ((ψ ≫ φ) ≫ f) σ.hom)).mapIso
          ((pullbackComp ψ φ).app F))
        ((pullback (baseChangeProj ((ψ ≫ φ) ≫ f) σ.hom)).mapIso
          ((pullbackComp ψ φ).app G))
        (homCast (Category.assoc ψ φ f).symm σ
          ((pullback ψ).obj ((pullback φ).obj F))
          ((pullback ψ).obj ((pullback φ).obj G))
          (restrictHomAlong (φ ≫ f) ((pullback φ).obj F) ((pullback φ).obj G) ψ σ
            (restrictHomAlong f F G φ σ u))) :=
  sorry

/-- The canonical structure morphism `X_ijk ⟶ X` along `pr₀`. -/
def tripleToX {ι : Type v} {Xi : ι → AlgebraicSpace S} (fi : (i : ι) → Xi i ⟶ X)
    {κ : ι → ι → Type w} {Xijk : (i j : ι) → κ i j → AlgebraicSpace S}
    (g : (i j : ι) → (k : κ i j) → Xijk i j k ⟶ Limits.pullback (fi i) (fi j))
    (i j : ι) (k : κ i j) : Xijk i j k ⟶ X :=
  g i j k ≫ Limits.pullback.fst (fi i) (fi j) ≫ fi i

/-- The two composites `X_ijk ⟶ X_i ×_X X_j ⟶ X` agree. -/
def tripleToX_snd_eq {ι : Type v} {Xi : ι → AlgebraicSpace S}
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
  (pullbackComp (g i j k ≫ Limits.pullback.fst (fi i) (fi j)) (fi i)).app F

/-- Pullback of `F_j` along `X_ijk ⟶ X_j` as pullback of `F` along `tripleToX`. -/
def triplePullbackSndIso {ι : Type v} {Xi : ι → AlgebraicSpace S}
    (fi : (i : ι) → Xi i ⟶ X) {κ : ι → ι → Type w}
    {Xijk : (i j : ι) → κ i j → AlgebraicSpace S}
    (g : (i j : ι) → (k : κ i j) → Xijk i j k ⟶ Limits.pullback (fi i) (fi j))
    (F : X.Modules) (i j : ι) (k : κ i j) :
    (pullback (g i j k ≫ Limits.pullback.snd (fi i) (fi j))).obj
        ((pullback (fi j)).obj F) ≅
      (pullback (tripleToX fi g i j k)).obj F :=
  (pullbackComp (g i j k ≫ Limits.pullback.snd (fi i) (fi j)) (fi j)).app F ≪≫
    (pullbackCongr (tripleToX_snd_eq fi g i j k)).app F

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
  homCongr
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
      homCongr
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
  homCongr
    ((pullback (baseChangeProj (tripleToX fi g i j k ≫ f) σ.hom)).mapIso
      (triplePullbackSndIso fi g F i j k))
    ((pullback (baseChangeProj (tripleToX fi g i j k ≫ f) σ.hom)).mapIso
      (triplePullbackSndIso fi g G i j k))
    (homCast
      ((Category.assoc
            (g i j k ≫ Limits.pullback.snd (fi i) (fi j)) (fi j) f).symm.trans
        (congrArg (fun p ↦ p ≫ f) (tripleToX_snd_eq fi g i j k)))
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
      homCongr
        ((pullback (baseChangeProj (tripleToX fi g i j k ≫ f) σ.hom)).mapIso
          (triplePullbackSndIso fi g F i j k))
        ((pullback (baseChangeProj (tripleToX fi g i j k ≫ f) σ.hom)).mapIso
          (triplePullbackSndIso fi g G i j k))
        (homCast
          ((Category.assoc
                (g i j k ≫ Limits.pullback.snd (fi i) (fi j)) (fi j) f).symm.trans
            (congrArg (fun p ↦ p ≫ f) (tripleToX_snd_eq fi g i j k)))
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


end AlgebraicGeometry.AlgebraicSpace.Modules
