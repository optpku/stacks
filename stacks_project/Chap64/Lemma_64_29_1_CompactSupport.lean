/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Sites.Whiskering
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
public import stacks_project.Chap59.Definition_59_70_1_ExtensionByZero
public import stacks_project.Chap59.Theorem_59_51_3_Cohomology

/-!
# Compactly supported geometric étale cohomology as a Galois module

This leaf owns `H_c^i(X_{k̄}, F)` as a `Gal(k̄/k)`-module, computed by extending `F`
by zero along a compactification and transporting the pullback Galois action of
Lemma 64.3.7 to coefficient universe `u+1`.
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

/-- Global cohomology of a pushforward sheaf agrees with cohomology of the source sheaf
on the pulled identity object, after transporting along `globalEtalePullbackIso`. -/
theorem pushforward_etaleCohomology₁_eq {S T : Scheme.{u}} (f : T ⟶ S)
    (H : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    etaleCohomology₁
        (((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            S.smallEtaleTopology T.smallEtaleTopology).obj H) n =
      etaleCohomology₁ H n :=
  sorry

/-- Pullback of `u+1`-coefficient global étale cohomology along a scheme morphism. -/
def cohomologyPullback₁ {S T : Scheme.{u}} (f : T ⟶ S)
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    etaleCohomology₁ G n ⟶
      etaleCohomology₁ ((etaleAbelianSheafPullback₁ f).obj G) n :=
  let pull := etaleAbelianSheafPullback₁ f
  let adj :=
    (smallEtalePullback f).sheafAdjunctionContinuous
      AddCommGrpCat.{u + 1} S.smallEtaleTopology T.smallEtaleTopology
  etaleCohomologyMap₁ (adj.unit.app G) n ≫
    eqToHom (pushforward_etaleCohomology₁_eq f (pull.obj G) n)

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

/-- The `G_k`-module `H^i(Y_{k̄}, F|_{Y_{k̄}})` at coefficient universe `u+1`. -/
def geometricEtaleCohomologyGaloisModule₁ (Y : SchemeOverField k)
    (F : Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) :
    Action AddCommGrpCat.{u + 1} Gal(AlgebraicClosure k/k) where
  V := geometricEtaleCohomology₁ Y F i
  ρ :=
    { toFun := fun σ ↦ galoisAction_geometricEtaleCohomology₁ Y F i σ
      map_one' := sorry
      map_mul' := sorry }

/-- Compactly supported geometric étale cohomology `H_c^i(X_{k̄}, F)` as a
`Gal(k̄/k)`-module, obtained by extending `F` by zero along a compactification. -/
def cohomologyCompactSupportGaloisModule (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) :
    Action AddCommGrpCat.{u + 1} Gal(AlgebraicClosure k/k) :=
  geometricEtaleCohomologyGaloisModule₁ P.obj.right
    ((etaleExtensionByZero (Compactification.Of.ι P) AddCommGrpCat.{u + 1}).obj F) i

/-- The underlying abelian group of compactly supported geometric cohomology. -/
theorem cohomologyCompactSupportGaloisModule_V (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) :
    (cohomologyCompactSupportGaloisModule X P F i).V =
      geometricEtaleCohomology₁ P.obj.right
        ((etaleExtensionByZero (Compactification.Of.ι P) AddCommGrpCat.{u + 1}).obj F) i :=
  rfl

/-- Evaluating the compactly supported Galois module recovers the pullback action. -/
theorem cohomologyCompactSupportGaloisModule_ρ (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ)
    (σ : Gal(AlgebraicClosure k/k)) :
    (cohomologyCompactSupportGaloisModule X P F i).ρ σ =
      galoisAction_geometricEtaleCohomology₁ P.obj.right
        ((etaleExtensionByZero (Compactification.Of.ι P) AddCommGrpCat.{u + 1}).obj F) i σ :=
  rfl

/-- Compactly supported geometric cohomology is independent of the compactification, up to
a canonical isomorphism of Galois modules. -/
theorem cohomologyCompactSupportGaloisModule_independent
    (X : SchemeOverField k)
    (P Q : Compactification.Of (Spec (CommRingCat.of k)) X)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) :
    Nonempty
      (cohomologyCompactSupportGaloisModule X P F i ≅
        cohomologyCompactSupportGaloisModule X Q F i) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
