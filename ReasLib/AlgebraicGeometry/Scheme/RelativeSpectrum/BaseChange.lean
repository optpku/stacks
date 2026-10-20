/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Basic

/-!
# Base change for the relative-spectrum functor

This leaf records an explicit pullback datum for quasi-coherent algebra sheaves
and the resulting functorial base-change comparison for relative spectra.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open Opposite
open RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S S' : Scheme.{u}}

/-- A point of the base change of a relative-spectrum functor along `g : S' ⟶ S`. -/
abbrev relativeSpectrumBaseChangePair
    (g : S' ⟶ S) (A : S.QcAlgebraUnder) (T : Scheme.{u}) : Type u :=
  Σ f' : T ⟶ S', A.obj ⟶ Under.mk (Hom.commRingSheafPushforwardMap (f' ≫ g).toShHom)

/-- The action on base-change relative-spectrum points induced by a morphism in `Schemeᵒᵖ`. -/
def relativeSpectrumBaseChangeFunctorMap
    (g : S' ⟶ S) (A : S.QcAlgebraUnder) {X Y : Schemeᵒᵖ} (a : X ⟶ Y) :
    relativeSpectrumBaseChangePair g A (unop X) →
      relativeSpectrumBaseChangePair g A (unop Y) :=
  fun x ↦
    (⟨unop a ≫ x.1, x.2 ≫ relativeSpectrumPairTargetMap (x.1 ≫ g) (unop a)⟩ :
      relativeSpectrumBaseChangePair g A (unop Y))

/-- A chosen pullback of a quasi-coherent algebra sheaf, specified by its universal mapping
property against structure-sheaf pushforwards. -/
structure RelativeSpectrumPullback
    (g : S' ⟶ S) (A : S.QcAlgebraUnder) (A' : S'.QcAlgebraUnder) where
  /-- Maps from the pulled-back algebra correspond to maps from the original algebra after
  composing with the base morphism. -/
  homEquiv :
    ∀ {T : Scheme.{u}} (f : T ⟶ S'),
      (A'.obj ⟶ Under.mk (Hom.commRingSheafPushforwardMap f.toShHom)) ≃
        (A.obj ⟶ Under.mk (Hom.commRingSheafPushforwardMap (f ≫ g).toShHom))
  /-- The comparison equivalences commute with precomposition of test schemes. -/
  homEquiv_naturality :
    ∀ {T T' : Scheme.{u}} (f : T' ⟶ S') (a : T ⟶ T')
      (φ : A'.obj ⟶ Under.mk (Hom.commRingSheafPushforwardMap f.toShHom)),
      homEquiv (a ≫ f) (φ ≫ relativeSpectrumPairTargetMap f a) =
        homEquiv f φ ≫ relativeSpectrumPairTargetMap (f ≫ g) a

/-- The base-change point map preserves identities. -/
theorem relativeSpectrumBaseChangeFunctorMap_id
    (g : S' ⟶ S) (A : S.QcAlgebraUnder) (T : Schemeᵒᵖ) :
    relativeSpectrumBaseChangeFunctorMap g A (𝟙 T) = id := sorry

/-- The base-change point map preserves composition. -/
theorem relativeSpectrumBaseChangeFunctorMap_comp
    (g : S' ⟶ S) (A : S.QcAlgebraUnder) {T T' T'' : Schemeᵒᵖ}
    (a : T ⟶ T') (b : T' ⟶ T'') :
    relativeSpectrumBaseChangeFunctorMap g A (a ≫ b) =
      relativeSpectrumBaseChangeFunctorMap g A b ∘ relativeSpectrumBaseChangeFunctorMap g A a := sorry

/-- The functor of points obtained by base-changing `relativeSpectrumFunctor A` along `g`. -/
def relativeSpectrumBaseChangeFunctor
    (g : S' ⟶ S) (A : S.QcAlgebraUnder) : Schemeᵒᵖ ⥤ Type u where
  obj T := relativeSpectrumBaseChangePair g A (unop T)
  map a := TypeCat.ofHom (relativeSpectrumBaseChangeFunctorMap g A a)
  map_id T := congrArg TypeCat.ofHom (relativeSpectrumBaseChangeFunctorMap_id g A T)
  map_comp a b := congrArg TypeCat.ofHom (relativeSpectrumBaseChangeFunctorMap_comp g A a b)

/-- The forward map on points in the relative-spectrum base-change comparison. -/
def relativeSpectrumFunctorBaseChangeIsoHomApp
    (A : S.QcAlgebraUnder) (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A') (T : Schemeᵒᵖ) :
    (relativeSpectrumFunctor A').obj T → (relativeSpectrumBaseChangeFunctor g A).obj T :=
  fun x ↦ ⟨x.1, pullbackData.homEquiv x.1 x.2⟩

/-- The inverse map on points in the relative-spectrum base-change comparison. -/
def relativeSpectrumFunctorBaseChangeIsoInvApp
    (A : S.QcAlgebraUnder) (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A') (T : Schemeᵒᵖ) :
    (relativeSpectrumBaseChangeFunctor g A).obj T → (relativeSpectrumFunctor A').obj T :=
  fun x ↦ ⟨x.1, (pullbackData.homEquiv x.1).symm x.2⟩

/-- The forward base-change comparison is natural in the test scheme. -/
theorem relativeSpectrumFunctorBaseChangeIso_hom_naturality
    (A : S.QcAlgebraUnder) (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A')
    {T T' : Schemeᵒᵖ} (a : T ⟶ T') :
    TypeCat.ofHom (relativeSpectrumFunctorMap A' a) ≫
        TypeCat.ofHom (relativeSpectrumFunctorBaseChangeIsoHomApp A g A' pullbackData T') =
      TypeCat.ofHom (relativeSpectrumFunctorBaseChangeIsoHomApp A g A' pullbackData T) ≫
        TypeCat.ofHom (relativeSpectrumBaseChangeFunctorMap g A a) := sorry

/-- The inverse base-change comparison is natural in the test scheme. -/
theorem relativeSpectrumFunctorBaseChangeIso_inv_naturality
    (A : S.QcAlgebraUnder) (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A')
    {T T' : Schemeᵒᵖ} (a : T ⟶ T') :
    TypeCat.ofHom (relativeSpectrumBaseChangeFunctorMap g A a) ≫
        TypeCat.ofHom (relativeSpectrumFunctorBaseChangeIsoInvApp A g A' pullbackData T') =
      TypeCat.ofHom (relativeSpectrumFunctorBaseChangeIsoInvApp A g A' pullbackData T) ≫
        TypeCat.ofHom (relativeSpectrumFunctorMap A' a) := sorry

/-- The forward natural transformation in the relative-spectrum base-change comparison. -/
def relativeSpectrumFunctorBaseChangeIsoHom
    (A : S.QcAlgebraUnder) (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A') :
    relativeSpectrumFunctor A' ⟶ relativeSpectrumBaseChangeFunctor g A where
  app T := TypeCat.ofHom (relativeSpectrumFunctorBaseChangeIsoHomApp A g A' pullbackData T)
  naturality := fun {T} {T'} a ↦
    relativeSpectrumFunctorBaseChangeIso_hom_naturality A g A' pullbackData (a : T ⟶ T')

/-- The inverse natural transformation in the relative-spectrum base-change comparison. -/
def relativeSpectrumFunctorBaseChangeIsoInv
    (A : S.QcAlgebraUnder) (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A') :
    relativeSpectrumBaseChangeFunctor g A ⟶ relativeSpectrumFunctor A' where
  app T := TypeCat.ofHom (relativeSpectrumFunctorBaseChangeIsoInvApp A g A' pullbackData T)
  naturality := fun {T} {T'} a ↦
    relativeSpectrumFunctorBaseChangeIso_inv_naturality A g A' pullbackData (a : T ⟶ T')

/-- The forward and inverse base-change transformations compose to the identity on the pulled-back
relative-spectrum functor. -/
theorem relativeSpectrumFunctorBaseChangeIso_hom_inv_id
    (A : S.QcAlgebraUnder) (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A') :
    relativeSpectrumFunctorBaseChangeIsoHom A g A' pullbackData ≫
        relativeSpectrumFunctorBaseChangeIsoInv A g A' pullbackData =
      𝟙 (relativeSpectrumFunctor A') := sorry

/-- The inverse and forward base-change transformations compose to the identity on the
base-changed relative-spectrum functor. -/
theorem relativeSpectrumFunctorBaseChangeIso_inv_hom_id
    (A : S.QcAlgebraUnder) (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A') :
    relativeSpectrumFunctorBaseChangeIsoInv A g A' pullbackData ≫
        relativeSpectrumFunctorBaseChangeIsoHom A g A' pullbackData =
      𝟙 (relativeSpectrumBaseChangeFunctor g A) := sorry

/-- The canonical natural isomorphism between the relative-spectrum functor of a chosen pullback
and the base change of the original relative-spectrum functor. -/
def relativeSpectrumFunctorBaseChangeIso
    (A : S.QcAlgebraUnder) (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A') :
    relativeSpectrumFunctor A' ≅ relativeSpectrumBaseChangeFunctor g A where
  hom := relativeSpectrumFunctorBaseChangeIsoHom A g A' pullbackData
  inv := relativeSpectrumFunctorBaseChangeIsoInv A g A' pullbackData
  hom_inv_id := relativeSpectrumFunctorBaseChangeIso_hom_inv_id A g A' pullbackData
  inv_hom_id := relativeSpectrumFunctorBaseChangeIso_inv_hom_id A g A' pullbackData

/-- The forward component of the base-change isomorphism is induced by `pullbackData.homEquiv`. -/
theorem relativeSpectrumFunctorBaseChangeIso_homApp
    (A : S.QcAlgebraUnder) (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A')
    (T : Schemeᵒᵖ) (x : (relativeSpectrumFunctor A').obj T) :
    (relativeSpectrumFunctorBaseChangeIso A g A' pullbackData).hom.app T x =
      ⟨x.1, pullbackData.homEquiv x.1 x.2⟩ := sorry

/-- The inverse component of the base-change isomorphism is induced by the inverse of
`pullbackData.homEquiv`. -/
theorem relativeSpectrumFunctorBaseChangeIso_invApp
    (A : S.QcAlgebraUnder) (g : S' ⟶ S) (A' : S'.QcAlgebraUnder)
    (pullbackData : RelativeSpectrumPullback g A A')
    (T : Schemeᵒᵖ) (x : (relativeSpectrumBaseChangeFunctor g A).obj T) :
    (relativeSpectrumFunctorBaseChangeIso A g A' pullbackData).inv.app T x =
      ⟨x.1, (pullbackData.homEquiv x.1).symm x.2⟩ := sorry

end AlgebraicGeometry.Scheme
