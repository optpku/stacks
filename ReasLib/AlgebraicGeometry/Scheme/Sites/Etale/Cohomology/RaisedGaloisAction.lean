module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Geometric Galois cohomology with raised coefficients

Inverse image on Ext defines pullback on global cohomology with coefficients one
universe above the scheme. Geometric base change carries its pullback Galois action.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Small-étale pullback admits left Kan extensions of `u+1`-coefficient abelian presheaves. -/
instance smallEtalePullback_op_hasLeftKanExtension_coeffSucc
    {S T : Scheme.{u}} (f : T ⟶ S) (G : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (smallEtalePullback f).op.HasLeftKanExtension G :=
  sorry

/-- Continuous sheaf pushforward along small-étale pullback is a right adjoint at coefficient
universe `u+1`. -/
instance instIsRightAdjoint_smallEtaleSheafPushforwardContinuous_coeffSucc
    {S T : Scheme.{u}} (f : T ⟶ S) :
    ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint :=
  sorry

/-- Small étale sites admit weak sheafification of `u+1`-coefficient abelian sheaves. -/
instance instHasWeakSheafify_smallEtaleAbelian_coeffSucc {Y : Scheme.{u}} :
    HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  sorry

/-- Small étale sites admit sheafification of `u+1`-coefficient abelian sheaves. -/
instance instHasSheafify_smallEtaleAbelian_coeffSucc {Y : Scheme.{u}} :
    HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  sorry

/-- Small étale abelian sheaf categories have Ext groups at coefficient universe `u+1`. -/
instance instHasExt_smallEtaleAbelian_coeffSucc {Y : Scheme.{u}} :
    HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  sorry

/-- Étale restriction admits left Kan extensions of `u+1`-coefficient abelian presheaves. -/
instance etaleRestriction_op_hasLeftKanExtension_coeffSucc
    {U Y : Scheme.{u}} (j : U ⟶ Y) [Etale j]
    (G : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (etaleRestriction j).op.HasLeftKanExtension G :=
  sorry

variable {k : Type u} [Field k]

/-- Inverse image of abelian sheaves at coefficient universe `u+1`. -/
abbrev etaleAbelianSheafPullback₁ {Z Z' : Scheme.{u}} (p : Z' ⟶ Z) :
    Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf Z'.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (smallEtalePullback p).sheafPullback AddCommGrpCat.{u + 1}
    Z.smallEtaleTopology Z'.smallEtaleTopology

/-- Pullback of `u+1`-coefficient abelian sheaves along a composite. -/
def etaleAbelianSheafPullback₁_comp {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B) :
    etaleAbelianSheafPullback₁ p ⋙ etaleAbelianSheafPullback₁ q ≅
      etaleAbelianSheafPullback₁ (q ≫ p) :=
  let siteIso :
      smallEtalePullback p ⋙ smallEtalePullback q ≅ smallEtalePullback (q ≫ p) :=
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) q p).symm
  Adjunction.leftAdjointCompIso
    ((smallEtalePullback p).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      A.smallEtaleTopology B.smallEtaleTopology)
    ((smallEtalePullback q).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      B.smallEtaleTopology C.smallEtaleTopology)
    ((smallEtalePullback (q ≫ p)).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      A.smallEtaleTopology C.smallEtaleTopology)
    (Functor.sheafPushforwardContinuousComp' siteIso AddCommGrpCat.{u + 1}
      A.smallEtaleTopology B.smallEtaleTopology C.smallEtaleTopology)

/-- Global étale cohomology of an `u+1`-coefficient abelian sheaf. -/
def etaleCohomology₁ {Y : Scheme.{u}}
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) :
    AddCommGrpCat.{u + 1} :=
  (Sheaf.cohomologyOverObjectFunctor.{u + 1, u + 1, u} Y.smallEtaleTopology
      (globalEtale Y) i).obj F

/-- The morphism on `u+1`-coefficient cohomology induced by a sheaf map. -/
def etaleCohomologyMap₁ {Y : Scheme.{u}}
    {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) (i : ℕ) :
    etaleCohomology₁ F i ⟶ etaleCohomology₁ G i :=
  (Sheaf.cohomologyOverObjectFunctor.{u + 1, u + 1, u} Y.smallEtaleTopology
      (globalEtale Y) i).map φ

/-- Geometric étale cohomology `H^i(Y_{k̄}, F|_{Y_{k̄}})` at coefficient universe `u+1`. -/
def geometricEtaleCohomology₁ (Y : SchemeOverField k)
    (F : Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) :
    AddCommGrpCat.{u + 1} :=
  etaleCohomology₁
    ((etaleAbelianSheafPullback₁
        (FieldExtension.toSource k (AlgebraicClosure k) Y.hom)).obj F)
    i

/-- Coefficient identification `(Spec(σ) × id)^{-1} (F|_{Y_{k̄}}) ≅ F|_{Y_{k̄}}`. -/
def galoisPastingIso₁ (Y : SchemeOverField k)
    (F : Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u + 1})
    (σ : Gal(AlgebraicClosure k/k)) :
    (etaleAbelianSheafPullback₁
        (FieldExtension.Galois.map k (AlgebraicClosure k) Y.hom σ)).obj
      ((etaleAbelianSheafPullback₁
          (FieldExtension.toSource k (AlgebraicClosure k) Y.hom)).obj F) ≅
      (etaleAbelianSheafPullback₁
          (FieldExtension.toSource k (AlgebraicClosure k) Y.hom)).obj F :=
  (etaleAbelianSheafPullback₁_comp
      (FieldExtension.toSource k (AlgebraicClosure k) Y.hom)
      (FieldExtension.Galois.map k (AlgebraicClosure k) Y.hom σ)).app F ≪≫
    (eqToIso
      (congrArg (fun h : FieldExtension.baseChange k (AlgebraicClosure k) Y.hom ⟶ Y.left ↦
          etaleAbelianSheafPullback₁ h)
        (FieldExtension.Galois.map_toSource k (AlgebraicClosure k) Y.hom σ))).app F

/-- Raised abelian inverse image is a left adjoint to continuous direct image. -/
instance etaleAbelianSheafPullback₁_isLeftAdjoint
    {S T : Scheme.{u}} (f : T ⟶ S) :
    (etaleAbelianSheafPullback₁ f).IsLeftAdjoint :=
  ((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    S.smallEtaleTopology T.smallEtaleTopology).isLeftAdjoint

/-- Raised abelian inverse image preserves finite limits. -/
instance etaleAbelianSheafPullback₁_preservesFiniteLimits
    {S T : Scheme.{u}} (f : T ⟶ S) :
    PreservesFiniteLimits (etaleAbelianSheafPullback₁ f) :=
  sorry

-- Local declaration justification (metaprogramming implementation): expose this private
-- implementation to the public pullback definition under Lean's module system.
set_option backward.privateInPublic true in
/-- Morphisms from the raised free abelian global representable are global sections. -/
private def raisedGeneratorHomEquiv (Y : Scheme.{u})
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (Y.smallEtaleTopology.freeAbelianSheaf (uliftYoneda.{u + 1}.obj (globalEtale Y)) ⟶ F) ≃
      F.obj.obj (Opposite.op (globalEtale Y)) :=
  ((sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _ F).trans
    ((FreeAbelianPresheaf.homEquiv
      (uliftYoneda.{u + 1}.obj (globalEtale Y)) F.obj).trans uliftYonedaEquiv)

-- Local declaration justification (metaprogramming implementation): expose this private
-- implementation to the public pullback definition under Lean's module system.
set_option backward.privateInPublic true in
/-- The raised global generator comparison is determined by the transported unit section. -/
private def raisedGeneratorPullbackHom {S T : Scheme.{u}} (f : T ⟶ S) :
    T.smallEtaleTopology.freeAbelianSheaf (uliftYoneda.{u + 1}.obj (globalEtale T)) ⟶
      (etaleAbelianSheafPullback₁ f).obj
        (S.smallEtaleTopology.freeAbelianSheaf (uliftYoneda.{u + 1}.obj (globalEtale S))) :=
  let generator :=
    S.smallEtaleTopology.freeAbelianSheaf (uliftYoneda.{u + 1}.obj (globalEtale S))
  let pull := etaleAbelianSheafPullback₁ f
  let generatorSection := raisedGeneratorHomEquiv S generator (𝟙 generator)
  let unitSection :=
    (((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      S.smallEtaleTopology T.smallEtaleTopology).unit.app generator).hom.app
        (Opposite.op (globalEtale S)) generatorSection
  (raisedGeneratorHomEquiv T (pull.obj generator)).symm
    ((pull.obj generator).obj.map (Opposite.op (globalEtalePullbackIso f).inv) unitSection)

-- Local declaration justification (metaprogramming implementation): Lean's module system
-- requires access to the private generator comparison in this public definition's body.
set_option backward.privateInPublic true in
/-- Pullback on raised global cohomology maps Ext by exact inverse image and precomposes
with the canonical global generator comparison. -/
def cohomologyPullback₁ {S T : Scheme.{u}} (f : T ⟶ S)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    etaleCohomology₁ G n ⟶
      etaleCohomology₁ ((etaleAbelianSheafPullback₁ f).obj G) n :=
  let pull := etaleAbelianSheafPullback₁ f
  let generator :=
    S.smallEtaleTopology.freeAbelianSheaf (uliftYoneda.{u + 1}.obj (globalEtale S))
  AddCommGrpCat.ofHom (pull.mapExtAddHom generator G n) ≫
    AddCommGrpCat.ofHom
      ((Abelian.Ext.mk₀ (raisedGeneratorPullbackHom f)).precomp (pull.obj G) (zero_add n))

/-- The Galois action `σ · ξ := (Spec(σ) × id)^* ξ` on geometric étale cohomology. -/
def galoisAction_geometricEtaleCohomology₁ (Y : SchemeOverField k)
    (F : Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ)
    (σ : Gal(AlgebraicClosure k/k)) :
    geometricEtaleCohomology₁ Y F i ⟶ geometricEtaleCohomology₁ Y F i :=
  cohomologyPullback₁
      (FieldExtension.Galois.map k (AlgebraicClosure k) Y.hom σ)
      ((etaleAbelianSheafPullback₁
          (FieldExtension.toSource k (AlgebraicClosure k) Y.hom)).obj F) i ≫
    etaleCohomologyMap₁ (galoisPastingIso₁ Y F σ).hom i

/-- Pullback endomorphisms of geometric cohomology satisfy the group-action laws. -/
theorem galoisAction_geometricEtaleCohomology₁_laws (Y : SchemeOverField k)
    (F : Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) :
    galoisAction_geometricEtaleCohomology₁ Y F i 1 = 𝟙 _ ∧
      ∀ σ τ : Gal(AlgebraicClosure k/k),
        galoisAction_geometricEtaleCohomology₁ Y F i (σ * τ) =
          galoisAction_geometricEtaleCohomology₁ Y F i τ ≫
            galoisAction_geometricEtaleCohomology₁ Y F i σ :=
  sorry

/-- The `G_k`-module `H^i(Y_{k̄}, F|_{Y_{k̄}})` at coefficient universe `u+1`. -/
def geometricEtaleCohomologyGaloisModule₁ (Y : SchemeOverField k)
    (F : Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) :
    Action AddCommGrpCat.{u + 1} Gal(AlgebraicClosure k/k) where
  V := geometricEtaleCohomology₁ Y F i
  ρ :=
    { toFun := fun σ ↦ galoisAction_geometricEtaleCohomology₁ Y F i σ
      map_one' := (galoisAction_geometricEtaleCohomology₁_laws Y F i).1
      map_mul' := (galoisAction_geometricEtaleCohomology₁_laws Y F i).2 }

end AlgebraicGeometry.Scheme.Etale

end
