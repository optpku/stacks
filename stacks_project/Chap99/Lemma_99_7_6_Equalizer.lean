/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import stacks_project.Chap66.Lemma_66_29_2
public import stacks_project.Chap73.Definition_73_9_1_FpqcCovering
public import stacks_project.Chap99.«99_7_1_1_Functor»
public import stacks_project.Chap99.«99_7_1_2_Functor»

/-!
# Restriction of quotient points along a covering of the total space

A morphism `φ : X' ⟶ X` over `B` induces restriction of kernel-identified
quotients of `F_T` along `X'_T ⟶ X_T`. An fpqc covering of `X` together with
coverings of the fibre products `X_i ×_X X_j` then yields the Čech parallel
pair on values of `Q_{F/X/B}` and of `Q^{fp}_{F/X/B}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The pasting isomorphism `X'_T ≅ X' ×_X X_T`. -/
def restrictSpaceIso (f : X ⟶ B) {X' : AlgebraicSpace S} (φ : X' ⟶ X)
    (σ : SchemesOver B) :
    fiber (φ ≫ f) σ ≅ pullback φ (pullback.fst f σ.hom) :=
  (pullbackRightPullbackFstIso f σ.hom φ).symm

/-- The canonical map `X'_T ⟶ X_T` induced by `φ : X' ⟶ X`. -/
def restrictSpaceMap (f : X ⟶ B) {X' : AlgebraicSpace S} (φ : X' ⟶ X)
    (σ : SchemesOver B) : fiber (φ ≫ f) σ ⟶ fiber f σ :=
  pullback.lift (pullback.fst (φ ≫ f) σ.hom ≫ φ) (pullback.snd (φ ≫ f) σ.hom)
    ((Category.assoc (pullback.fst (φ ≫ f) σ.hom) φ f).trans
      (pullback.condition :
        pullback.fst (φ ≫ f) σ.hom ≫ φ ≫ f =
          pullback.snd (φ ≫ f) σ.hom ≫ σ.hom))

/-- `restrictSpaceMap` commutes with the projections to `X`. -/
def restrictSpaceMap_comp_proj (f : X ⟶ B) {X' : AlgebraicSpace S} (φ : X' ⟶ X)
    (σ : SchemesOver B) :
    restrictSpaceMap f φ σ ≫ pullback.fst f σ.hom =
      pullback.fst (φ ≫ f) σ.hom ≫ φ :=
  pullback.lift_fst (pullback.fst (φ ≫ f) σ.hom ≫ φ) (pullback.snd (φ ≫ f) σ.hom)
    ((Category.assoc (pullback.fst (φ ≫ f) σ.hom) φ f).trans
      (pullback.condition :
        pullback.fst (φ ≫ f) σ.hom ≫ φ ≫ f =
          pullback.snd (φ ≫ f) σ.hom ≫ σ.hom))

/-- Identification of `(φ^* F)_T` with the pullback of `F_T` along `X'_T ⟶ X_T`. -/
def restrictFiberFIso (f : X ⟶ B) {X' : AlgebraicSpace S} (φ : X' ⟶ X)
    (σ : SchemesOver B) (F : X.Modules) :
    fiberF (φ ≫ f) ((Modules.pullback φ).obj F) σ ≅
      (Modules.pullback (restrictSpaceMap f φ σ)).obj (fiberF f F σ) :=
  (Modules.pullbackComp (pullback.fst (φ ≫ f) σ.hom) φ).app F ≪≫
    eqToIso (congrArg (fun ψ ↦ (Modules.pullback ψ).obj F)
      (restrictSpaceMap_comp_proj f φ σ).symm) ≪≫
    (Modules.pullbackComp (restrictSpaceMap f φ σ)
      (pullback.fst f σ.hom)).symm.app F

namespace Point

/-- Source-transport a quotient point along an isomorphism of the ambient module
`F_T`. -/
def congrModule {X' : AlgebraicSpace S} {α : X' ⟶ B} {F G : X'.Modules}
    {σ : SchemesOver B} (e : F ≅ G) (Q : Point α F σ) : Point α G σ where
  module := Q.module
  map := (Modules.pullback (pullback.fst α σ.hom)).map e.inv ≫ Q.map
  map_epi := sorry
  isQuasicoherent := Q.isQuasicoherent
  isFlat := Q.isFlat

/-- Transport a quotient point along an equality of structure morphisms over `B`
and an isomorphism of source modules. -/
def congr {X' : AlgebraicSpace S} {α β : X' ⟶ B} (h : α = β) {F G : X'.Modules}
    (e : F ≅ G) {σ : SchemesOver B} (Q : Point α F σ) : Point β G σ :=
  eqToHom (congrArg (fun γ ↦ Point γ G σ) h) (Q.congrModule e)

/-- Restriction of a quotient point of `F_T` along `φ : X' ⟶ X`. -/
def restrictAlong {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    {X' : AlgebraicSpace S} (Q : Point f F σ) (φ : X' ⟶ X) :
    Point (φ ≫ f) ((Modules.pullback φ).obj F) σ where
  module := (Modules.pullback (restrictSpaceMap f φ σ)).obj Q.module
  map := (restrictFiberFIso f φ σ F).hom ≫
    (Modules.pullback (restrictSpaceMap f φ σ)).map Q.map
  map_epi := sorry
  isQuasicoherent := sorry
  isFlat := sorry

/-- The module of a restricted quotient point is the module pullback along
`restrictSpaceMap`. -/
theorem restrictAlong_module {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    {X' : AlgebraicSpace S} (Q : Point f F σ) (φ : X' ⟶ X) :
    (Q.restrictAlong φ).module =
      (Modules.pullback (restrictSpaceMap f φ σ)).obj Q.module :=
  sorry

/-- The restricted quotient map is the pullback of `Q.map` after
`restrictFiberFIso`. -/
theorem restrictAlong_map {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    {X' : AlgebraicSpace S} (Q : Point f F σ) (φ : X' ⟶ X) :
    (Q.restrictAlong φ).map =
      (restrictFiberFIso f φ σ F).hom ≫
        (Modules.pullback (restrictSpaceMap f φ σ)).map Q.map :=
  sorry

end Point

/-- Restriction of quotient points along `φ : X' ⟶ X` preserves kernel
identification. -/
theorem restrictAlong_rel (f : X ⟶ B) (F : X.Modules) {X' : AlgebraicSpace S}
    (φ : X' ⟶ X) (σ : SchemesOver B) :
    ∀ (Q₁ Q₂ : Point f F σ),
      (quotientSetoid f F σ).r Q₁ Q₂ →
        (quotientSetoid (φ ≫ f) ((Modules.pullback φ).obj F) σ).r
          (Q₁.restrictAlong φ) (Q₂.restrictAlong φ) :=
  sorry

/-- Restriction of kernel-identified quotients of `F_T` along `φ : X' ⟶ X`. -/
def restrictAlong (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {X' : AlgebraicSpace S} (φ : X' ⟶ X) (σ : SchemesOver B) :
    (functor f F).obj (op σ) →
      (functor (φ ≫ f) ((Modules.pullback φ).obj F)).obj (op σ) :=
  _root_.Quotient.map (fun Q : Point f F σ ↦ Q.restrictAlong φ)
    (restrictAlong_rel f F φ σ)

/-- Restriction of kernel-identified quotients evaluates on a representative by
`Point.restrictAlong`. -/
theorem restrictAlong_apply (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {X' : AlgebraicSpace S} (φ : X' ⟶ X) (σ : SchemesOver B)
    (Q : Point f F σ) :
    restrictAlong f F φ σ (Quotient.mk (quotientSetoid f F σ) Q) =
      Quotient.mk (quotientSetoid (φ ≫ f) ((Modules.pullback φ).obj F) σ)
        (Q.restrictAlong φ) :=
  sorry

namespace FpPoint

/-- Source-transport a finitely presented quotient point along an isomorphism of
the ambient module `F_T`. -/
def congrModule {X' : AlgebraicSpace S} {α : X' ⟶ B} {F G : X'.Modules}
    {σ : SchemesOver B} (e : F ≅ G) (Q : FpPoint α F σ) : FpPoint α G σ where
  point := Q.point.congrModule e
  isFinitePresentation := Q.isFinitePresentation

/-- Transport a finitely presented quotient point along an equality of structure
morphisms over `B` and an isomorphism of source modules. -/
def congr {X' : AlgebraicSpace S} {α β : X' ⟶ B} (h : α = β) {F G : X'.Modules}
    (e : F ≅ G) {σ : SchemesOver B} (Q : FpPoint α F σ) : FpPoint β G σ :=
  eqToHom (congrArg (fun γ ↦ FpPoint γ G σ) h) (Q.congrModule e)

/-- Restriction of a finitely presented quotient point of `F_T` along
`φ : X' ⟶ X`. -/
def restrictAlong {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    {X' : AlgebraicSpace S} (Q : FpPoint f F σ) (φ : X' ⟶ X) :
    FpPoint (φ ≫ f) ((Modules.pullback φ).obj F) σ where
  point := Q.point.restrictAlong φ
  isFinitePresentation := sorry

/-- The underlying point of a restricted `FpPoint` is the restricted point. -/
theorem restrictAlong_point {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    {X' : AlgebraicSpace S} (Q : FpPoint f F σ) (φ : X' ⟶ X) :
    (Q.restrictAlong φ).point = Q.point.restrictAlong φ :=
  sorry

end FpPoint

/-- Restriction of finitely presented quotient points along `φ : X' ⟶ X`
preserves kernel identification. -/
theorem fpRestrictAlong_rel (f : X ⟶ B) (F : X.Modules) {X' : AlgebraicSpace S}
    (φ : X' ⟶ X) (σ : SchemesOver B) :
    ∀ (Q₁ Q₂ : FpPoint f F σ),
      (fpSetoid f F σ).r Q₁ Q₂ →
        (fpSetoid (φ ≫ f) ((Modules.pullback φ).obj F) σ).r
          (Q₁.restrictAlong φ) (Q₂.restrictAlong φ) :=
  sorry

/-- Restriction of kernel-identified finitely presented quotients of `F_T` along
`φ : X' ⟶ X`. -/
def fpRestrictAlong (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {X' : AlgebraicSpace S} (φ : X' ⟶ X) (σ : SchemesOver B) :
    (fpFunctor f F).obj (op σ) →
      (fpFunctor (φ ≫ f) ((Modules.pullback φ).obj F)).obj (op σ) :=
  _root_.Quotient.map (fun Q : FpPoint f F σ ↦ Q.restrictAlong φ)
    (fpRestrictAlong_rel f F φ σ)

/-- Restriction of finitely presented quotient classes evaluates on a
representative by `FpPoint.restrictAlong`. -/
theorem fpRestrictAlong_apply (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {X' : AlgebraicSpace S} (φ : X' ⟶ X) (σ : SchemesOver B)
    (Q : FpPoint f F σ) :
    fpRestrictAlong f F φ σ (Quotient.mk (fpSetoid f F σ) Q) =
      Quotient.mk (fpSetoid (φ ≫ f) ((Modules.pullback φ).obj F) σ)
        (Q.restrictAlong φ) :=
  sorry

/-- Transport of kernel-identified quotients along an equality of structure
morphisms over `B` preserves kernel identification. -/
theorem functorCongr_rel {X' : AlgebraicSpace S} {α β : X' ⟶ B} (h : α = β)
    {F G : X'.Modules} (e : F ≅ G) (σ : SchemesOver B) :
    ∀ (Q₁ Q₂ : Point α F σ),
      (quotientSetoid α F σ).r Q₁ Q₂ →
        (quotientSetoid β G σ).r (Point.congr h e Q₁) (Point.congr h e Q₂) :=
  sorry

/-- Transport of kernel-identified quotients along an equality of structure
morphisms over `B` and an isomorphism of source modules. -/
def functorCongr {X' : AlgebraicSpace S} {α β : X' ⟶ B} (h : α = β)
    {F G : X'.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (e : F ≅ G)
    (σ : SchemesOver B) :
    (functor α F).obj (op σ) → (functor β G).obj (op σ) :=
  _root_.Quotient.map (fun Q : Point α F σ ↦ Point.congr h e Q)
    (functorCongr_rel h e σ)

/-- Transport of finitely presented quotient classes along an equality of
structure morphisms over `B` preserves kernel identification. -/
theorem fpFunctorCongr_rel {X' : AlgebraicSpace S} {α β : X' ⟶ B} (h : α = β)
    {F G : X'.Modules} (e : F ≅ G) (σ : SchemesOver B) :
    ∀ (Q₁ Q₂ : FpPoint α F σ),
      (fpSetoid α F σ).r Q₁ Q₂ →
        (fpSetoid β G σ).r (FpPoint.congr h e Q₁) (FpPoint.congr h e Q₂) :=
  sorry

/-- Transport of finitely presented quotient classes along an equality of
structure morphisms over `B` and an isomorphism of source modules. -/
def fpFunctorCongr {X' : AlgebraicSpace S} {α β : X' ⟶ B} (h : α = β)
    {F G : X'.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (e : F ≅ G)
    (σ : SchemesOver B) :
    (fpFunctor α F).obj (op σ) → (fpFunctor β G).obj (op σ) :=
  _root_.Quotient.map (fun Q : FpPoint α F σ ↦ FpPoint.congr h e Q)
    (fpFunctorCongr_rel h e σ)

/-- The composite `X_ijk ⟶ X` of an overlap member with `pr₀` and `X_i ⟶ X`. -/
def tripleToX {I : Type v} (family : I → Over X) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (i j : I) (k : K i j) : (overlap i j k).left ⟶ X :=
  (overlap i j k).hom ≫ pullback.fst (family i).hom (family j).hom ≫
    (family i).hom

/-- The first projection composite of an overlap member recovers `tripleToX`. -/
def tripleToX_fst_eq {I : Type v} (family : I → Over X) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (i j : I) (k : K i j) :
    ((overlap i j k).hom ≫ pullback.fst (family i).hom (family j).hom) ≫
        (family i).hom =
      tripleToX family overlap i j k :=
  Category.assoc (overlap i j k).hom
    (pullback.fst (family i).hom (family j).hom) (family i).hom

/-- The second projection composite of an overlap member recovers `tripleToX`. -/
def tripleToX_snd_eq {I : Type v} (family : I → Over X) {K : I → I → Type w}
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
def tripleToX_fst_comp_eq (f : X ⟶ B) {I : Type v} (family : I → Over X)
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
def tripleToX_snd_comp_eq (f : X ⟶ B) {I : Type v} (family : I → Over X)
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
  (Modules.pullbackComp
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
  (Modules.pullbackComp
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
    (family : I → Over X) (σ : SchemesOver B)
    (u : (functor f F).obj (op σ)) (i : I) :
    (memberFunctor f F family i).obj (op σ) :=
  restrictAlong f F (family i).hom σ u

/-- `coveringHom` is restriction along each `X_i ⟶ X`. -/
theorem coveringHom_apply (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {I : Type v} (family : I → Over X) (σ : SchemesOver B)
    (u : (functor f F).obj (op σ)) (i : I) :
    coveringHom f F family σ u i = restrictAlong f F (family i).hom σ u :=
  sorry

/-- The parallel arrow `pr₀^*`, restricting each class on `X_i` along
`X_ijk ⟶ X_i`. -/
def coveringPrFst (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    (family : I → Over X) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (σ : SchemesOver B)
    (s : (i : I) → (memberFunctor f F family i).obj (op σ)) (i j : I)
    (k : K i j) : (overlapFunctor f F family overlap i j k).obj (op σ) :=
  functorCongr (tripleToX_fst_comp_eq f family overlap i j k)
    (overlapPullbackFstIso F family overlap i j k) σ
    (restrictAlong ((family i).hom ≫ f)
      ((Modules.pullback (family i).hom).obj F)
      ((overlap i j k).hom ≫ pullback.fst (family i).hom (family j).hom) σ
      (s i))

/-- `coveringPrFst` is restriction along `X_ijk ⟶ X_i`, transported to
`tripleToX`. -/
theorem coveringPrFst_apply (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {I : Type v} (family : I → Over X) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (σ : SchemesOver B)
    (s : (i : I) → (memberFunctor f F family i).obj (op σ)) (i j : I)
    (k : K i j) :
    coveringPrFst f F family overlap σ s i j k =
      functorCongr (tripleToX_fst_comp_eq f family overlap i j k)
        (overlapPullbackFstIso F family overlap i j k) σ
        (restrictAlong ((family i).hom ≫ f)
          ((Modules.pullback (family i).hom).obj F)
          ((overlap i j k).hom ≫ pullback.fst (family i).hom (family j).hom) σ
          (s i)) :=
  sorry

/-- The parallel arrow `pr₁^*`, restricting each class on `X_j` along
`X_ijk ⟶ X_j`. -/
def coveringPrSnd (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    (family : I → Over X) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (σ : SchemesOver B)
    (s : (i : I) → (memberFunctor f F family i).obj (op σ)) (i j : I)
    (k : K i j) : (overlapFunctor f F family overlap i j k).obj (op σ) :=
  functorCongr (tripleToX_snd_comp_eq f family overlap i j k)
    (overlapPullbackSndIso F family overlap i j k) σ
    (restrictAlong ((family j).hom ≫ f)
      ((Modules.pullback (family j).hom).obj F)
      ((overlap i j k).hom ≫ pullback.snd (family i).hom (family j).hom) σ
      (s j))

/-- `coveringPrSnd` is restriction along `X_ijk ⟶ X_j`, transported to
`tripleToX`. -/
theorem coveringPrSnd_apply (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {I : Type v} (family : I → Over X) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (σ : SchemesOver B)
    (s : (i : I) → (memberFunctor f F family i).obj (op σ)) (i j : I)
    (k : K i j) :
    coveringPrSnd f F family overlap σ s i j k =
      functorCongr (tripleToX_snd_comp_eq f family overlap i j k)
        (overlapPullbackSndIso F family overlap i j k) σ
        (restrictAlong ((family j).hom ≫ f)
          ((Modules.pullback (family j).hom).obj F)
          ((overlap i j k).hom ≫ pullback.snd (family i).hom (family j).hom) σ
          (s j)) :=
  sorry

/-- The two Čech restrictions of a global class in `Q_{F/X/B}(T)` agree. -/
theorem covering_equalizes (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {I : Type v} (family : I → Over X) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (σ : SchemesOver B) (u : (functor f F).obj (op σ)) :
    coveringPrFst f F family overlap σ (coveringHom f F family σ u) =
      coveringPrSnd f F family overlap σ (coveringHom f F family σ u) :=
  sorry

/-- The first arrow of the Čech diagram for `Q^{fp}_{F/X/B}`. -/
def fpCoveringHom (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    (family : I → Over X) (σ : SchemesOver B)
    (u : (fpFunctor f F).obj (op σ)) (i : I) :
    (fpMemberFunctor f F family i).obj (op σ) :=
  fpRestrictAlong f F (family i).hom σ u

/-- `fpCoveringHom` is restriction along each `X_i ⟶ X`. -/
theorem fpCoveringHom_apply (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {I : Type v} (family : I → Over X) (σ : SchemesOver B)
    (u : (fpFunctor f F).obj (op σ)) (i : I) :
    fpCoveringHom f F family σ u i = fpRestrictAlong f F (family i).hom σ u :=
  sorry

/-- The parallel arrow `pr₀^*` for `Q^{fp}_{F/X/B}`. -/
def fpCoveringPrFst (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    (family : I → Over X) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (σ : SchemesOver B)
    (s : (i : I) → (fpMemberFunctor f F family i).obj (op σ)) (i j : I)
    (k : K i j) : (fpOverlapFunctor f F family overlap i j k).obj (op σ) :=
  fpFunctorCongr (tripleToX_fst_comp_eq f family overlap i j k)
    (overlapPullbackFstIso F family overlap i j k) σ
    (fpRestrictAlong ((family i).hom ≫ f)
      ((Modules.pullback (family i).hom).obj F)
      ((overlap i j k).hom ≫ pullback.fst (family i).hom (family j).hom) σ
      (s i))

/-- `fpCoveringPrFst` is restriction along `X_ijk ⟶ X_i`, transported to
`tripleToX`. -/
theorem fpCoveringPrFst_apply (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {I : Type v} (family : I → Over X) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (σ : SchemesOver B)
    (s : (i : I) → (fpMemberFunctor f F family i).obj (op σ)) (i j : I)
    (k : K i j) :
    fpCoveringPrFst f F family overlap σ s i j k =
      fpFunctorCongr (tripleToX_fst_comp_eq f family overlap i j k)
        (overlapPullbackFstIso F family overlap i j k) σ
        (fpRestrictAlong ((family i).hom ≫ f)
          ((Modules.pullback (family i).hom).obj F)
          ((overlap i j k).hom ≫ pullback.fst (family i).hom (family j).hom) σ
          (s i)) :=
  sorry

/-- The parallel arrow `pr₁^*` for `Q^{fp}_{F/X/B}`. -/
def fpCoveringPrSnd (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] {I : Type v}
    (family : I → Over X) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (σ : SchemesOver B)
    (s : (i : I) → (fpMemberFunctor f F family i).obj (op σ)) (i j : I)
    (k : K i j) : (fpOverlapFunctor f F family overlap i j k).obj (op σ) :=
  fpFunctorCongr (tripleToX_snd_comp_eq f family overlap i j k)
    (overlapPullbackSndIso F family overlap i j k) σ
    (fpRestrictAlong ((family j).hom ≫ f)
      ((Modules.pullback (family j).hom).obj F)
      ((overlap i j k).hom ≫ pullback.snd (family i).hom (family j).hom) σ
      (s j))

/-- `fpCoveringPrSnd` is restriction along `X_ijk ⟶ X_j`, transported to
`tripleToX`. -/
theorem fpCoveringPrSnd_apply (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {I : Type v} (family : I → Over X) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (σ : SchemesOver B)
    (s : (i : I) → (fpMemberFunctor f F family i).obj (op σ)) (i j : I)
    (k : K i j) :
    fpCoveringPrSnd f F family overlap σ s i j k =
      fpFunctorCongr (tripleToX_snd_comp_eq f family overlap i j k)
        (overlapPullbackSndIso F family overlap i j k) σ
        (fpRestrictAlong ((family j).hom ≫ f)
          ((Modules.pullback (family j).hom).obj F)
          ((overlap i j k).hom ≫ pullback.snd (family i).hom (family j).hom) σ
          (s j)) :=
  sorry

/-- The two Čech restrictions of a global class in `Q^{fp}_{F/X/B}(T)` agree. -/
theorem fp_covering_equalizes (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {I : Type v} (family : I → Over X) {K : I → I → Type w}
    (overlap : ∀ i j, K i j → Over (pullback (family i).hom (family j).hom))
    (σ : SchemesOver B) (u : (fpFunctor f F).obj (op σ)) :
    fpCoveringPrFst f F family overlap σ (fpCoveringHom f F family σ u) =
      fpCoveringPrSnd f F family overlap σ (fpCoveringHom f F family σ u) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
