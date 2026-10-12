/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Definition_98_13_1_Versal
public import stacks_project.Chap98.Lemma_98_27_6_Solution
public import stacks_project.Chap98.Lemma_98_27_13_TangentSpace

/-!
# Versality of sections of Type-valued functors

A section of a Type-valued functor on locally Noetherian schemes over a
locally Noetherian base is versal at a finite type point when restriction
along pointed maps `Spec(A) ⟶ V` has the Schlessinger lifting property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver (residueFieldType fromResidueField)
open AlgebraicGeometry.GroupoidsOver.Predeformation
open AlgebraicGeometry.AlgebraicSpace (ofOver homOnLocallyNoetherian)

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Over

/-- The structure morphism `Spec(κ(v0)) ⟶ S`. -/
abbrev residueToS {S : Scheme.{u}} (V : Over S) (v0 : V.left) :
    Spec (CommRingCat.of (residueFieldType v0)) ⟶ S :=
  fromResidueField v0 ≫ V.hom

/-- The residue-field point `Spec(κ(v0)) ⟶ V` as a morphism of `Over S`. -/
def fromResidueOver {S : Scheme.{u}} (V : Over S) (v0 : V.left) :
    Over.mk (residueToS V v0) ⟶ V :=
  Over.homMk (fromResidueField v0) rfl

/-- The underlying scheme morphism of `fromResidueOver` is `fromResidueField`. -/
theorem fromResidueOver_left {S : Scheme.{u}} (V : Over S) (v0 : V.left) :
    (fromResidueOver V v0).left = fromResidueField v0 :=
  sorry

/-- Restriction of a section of a Type-valued functor along a morphism of
locally Noetherian schemes over `S`. -/
def restrictAlong {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v)
    {V : Over S} [IsLocallyNoetherian V.left]
    (ξ : F.obj (op (asLocallyNoetherian V))) {W : Over S}
    [IsLocallyNoetherian W.left] (f : W ⟶ V) :
    F.obj (op (asLocallyNoetherian W)) :=
  F.map (op (asLocallyNoetherianMap f)) ξ

/-- `restrictAlong` is the action of `F.map` on `asLocallyNoetherianMap`. -/
theorem restrictAlong_eq {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v)
    {V : Over S} [IsLocallyNoetherian V.left]
    (ξ : F.obj (op (asLocallyNoetherian V))) {W : Over S}
    [IsLocallyNoetherian W.left] (f : W ⟶ V) :
    restrictAlong F ξ f = F.map (op (asLocallyNoetherianMap f)) ξ :=
  sorry

/-- Restriction along the identity morphism recovers the original section. -/
theorem restrictAlong_id {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v)
    {V : Over S} [IsLocallyNoetherian V.left]
    (ξ : F.obj (op (asLocallyNoetherian V))) :
    restrictAlong F ξ (𝟙 V) = ξ :=
  sorry

/-- Restriction is contravariant in the test morphism. -/
theorem restrictAlong_comp {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v)
    {U V W : Over S} [IsLocallyNoetherian U.left] [IsLocallyNoetherian V.left]
    [IsLocallyNoetherian W.left] (f : V ⟶ W) (g : U ⟶ V)
    (ξ : F.obj (op (asLocallyNoetherian W))) :
    restrictAlong F ξ (g ≫ f) = restrictAlong F (restrictAlong F ξ f) g :=
  sorry

/-- The canonical morphism `Spec(κ(v0)) ⟶ Spec(A)` over `S`. -/
def specOverToResidue {S : Scheme.{u}} [IsLocallyNoetherian S] {V : Over S}
    [LocallyOfFiniteType V.hom] (v0 : V.left) [IsFiniteTypePoint v0]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (residueFieldType v0)] [Module.Finite Λ (residueFieldType v0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType v0))) ≫
          openImmersion =
        residueToS V v0)
    (A : ArtinianLocalAlgCat Λ (residueFieldType v0)) :
    Over.mk (residueToS V v0) ⟶ specOver openImmersion A :=
  specOver_toResidue openImmersion (residueToS V v0) h_factor A

/-- `specOverToResidue` is `specOver_toResidue` at `residueToS V v0`. -/
theorem specOverToResidue_eq {S : Scheme.{u}} [IsLocallyNoetherian S]
    {V : Over S} [LocallyOfFiniteType V.hom] (v0 : V.left)
    [IsFiniteTypePoint v0] {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (residueFieldType v0)] [Module.Finite Λ (residueFieldType v0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType v0))) ≫
          openImmersion =
        residueToS V v0)
    (A : ArtinianLocalAlgCat Λ (residueFieldType v0)) :
    specOverToResidue v0 openImmersion h_factor A =
      specOver_toResidue openImmersion (residueToS V v0) h_factor A :=
  sorry

/-- Infinitesimal lifting of pointed maps `Spec(A) ⟶ V` against restriction of
`ξ`, relative to one affine-open factorization of `Spec(κ(v0)) ⟶ S`. -/
def IsSmoothRestriction {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v)
    {V : Over S} [IsLocallyNoetherian V.left] [LocallyOfFiniteType V.hom]
    (ξ : F.obj (op (asLocallyNoetherian V))) (v0 : V.left)
    [IsFiniteTypePoint v0] {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (residueFieldType v0)] [Module.Finite Λ (residueFieldType v0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType v0))) ≫
          openImmersion =
        residueToS V v0) : Prop :=
  ∀ {B A : ArtinianLocalAlgCat Λ (residueFieldType v0)} (f : B ⟶ A),
    Function.Surjective f.hom →
      ∀ (φ : specOver openImmersion A ⟶ V)
        (η : F.obj (op (asLocallyNoetherian (specOver openImmersion B)))),
        specOverToResidue v0 openImmersion h_factor A ≫ φ =
            fromResidueOver V v0 →
          restrictAlong F η (specOverToResidue v0 openImmersion h_factor B) =
              restrictAlong F ξ (fromResidueOver V v0) →
            restrictAlong F ξ φ =
                restrictAlong F η (specOverMap openImmersion f) →
              ∃ φ' : specOver openImmersion B ⟶ V,
                specOverMap openImmersion f ≫ φ' = φ ∧
                  restrictAlong F ξ φ' = η

/-- A section `ξ` of `F` on a scheme `V` locally of finite type over `S` is
versal at a finite type point `v0` when restriction of `ξ` along pointed maps
`Spec(A) ⟶ V` at `v0` is smooth on every affine-open factorization of
`Spec(κ(v0)) ⟶ S`. -/
class IsVersalAt {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v)
    {V : Over S} [IsLocallyNoetherian V.left] [LocallyOfFiniteType V.hom]
    (ξ : F.obj (op (asLocallyNoetherian V))) (v0 : V.left) : Prop where
  /-- Smoothness of restriction of `ξ` at `v0` on every affine-open
  factorization of `Spec(κ(v0)) ⟶ S`. -/
  exists_lift :
    ∀ [IsFiniteTypePoint v0] {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
      [Algebra Λ (residueFieldType v0)] [Module.Finite Λ (residueFieldType v0)]
      (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
      [IsOpenImmersion openImmersion]
      (h_factor :
        Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType v0))) ≫
            openImmersion =
          residueToS V v0),
      IsSmoothRestriction F ξ v0 openImmersion h_factor

/-- The identity section of `homOnLocallyNoetherian (ofOver V)` is versal at
every finite type point of `V`. -/
instance instIsVersalAt_id {S : Scheme.{u}} [IsLocallyNoetherian S]
    {V : Over S} [IsLocallyNoetherian V.left] [LocallyOfFiniteType V.hom]
    (v0 : V.left) [IsFiniteTypePoint v0] :
    IsVersalAt (homOnLocallyNoetherian (ofOver V)) (𝟙 (ofOver V)) v0 :=
  sorry

namespace IsVersalAt

/-- Versality at `v0` supplies the Schlessinger lifting property of restriction
of `ξ` on every affine-open factorization of `Spec(κ(v0)) ⟶ S`. -/
theorem spec {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v)
    {V : Over S} [IsLocallyNoetherian V.left] [LocallyOfFiniteType V.hom]
    (ξ : F.obj (op (asLocallyNoetherian V))) (v0 : V.left)
    [IsFiniteTypePoint v0] [IsVersalAt F ξ v0] {Λ : Type u} [CommRing Λ]
    [IsNoetherianRing Λ] [Algebra Λ (residueFieldType v0)]
    [Module.Finite Λ (residueFieldType v0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType v0))) ≫
          openImmersion =
        residueToS V v0) :
    IsSmoothRestriction F ξ v0 openImmersion h_factor :=
  sorry

/-- Versality at `v0` is smoothness of restriction of `ξ` on every affine-open
factorization of `Spec(κ(v0)) ⟶ S`. -/
theorem iff {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v)
    {V : Over S} [IsLocallyNoetherian V.left] [LocallyOfFiniteType V.hom]
    (ξ : F.obj (op (asLocallyNoetherian V))) (v0 : V.left)
    [IsFiniteTypePoint v0] :
    IsVersalAt F ξ v0 ↔
      ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
        [Algebra Λ (residueFieldType v0)] [Module.Finite Λ (residueFieldType v0)]
        (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
        [IsOpenImmersion openImmersion]
        (h_factor :
          Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType v0))) ≫
              openImmersion =
            residueToS V v0),
        IsSmoothRestriction F ξ v0 openImmersion h_factor :=
  sorry

end IsVersalAt

/-- Unfolding `IsVersalAt` recovers smoothness of restriction of `ξ` at `v0`. -/
theorem isVersalAt_iff {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v)
    {V : Over S} [IsLocallyNoetherian V.left] [LocallyOfFiniteType V.hom]
    (ξ : F.obj (op (asLocallyNoetherian V))) (v0 : V.left)
    [IsFiniteTypePoint v0] :
    IsVersalAt F ξ v0 ↔
      ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
        [Algebra Λ (residueFieldType v0)] [Module.Finite Λ (residueFieldType v0)]
        (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
        [IsOpenImmersion openImmersion]
        (h_factor :
          Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType v0))) ≫
              openImmersion =
            residueToS V v0),
        IsSmoothRestriction F ξ v0 openImmersion h_factor :=
  sorry

end AlgebraicGeometry.Scheme.Over
