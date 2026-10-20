/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.Comparison

/-!
# Base change for degreewise relative projective-spectrum functors

This leaf turns explicit graded pullback and pointwise comparison data into a
natural isomorphism of functors on test schemes.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S S' : Scheme.{u}}
variable {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf}
variable {d : ℕ}

/-- The raw forward point map in the base-change comparison of degreewise relative
projective-spectrum functors. -/
def relativeProjDegreeFunctorBaseChangeIsoHomApp
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison : RelativeProjDegreeFunctorBaseChangeComparison g F_d 𝒜' F'_d)
    (T : Schemeᵒᵖ) :
    F'_d.toFunctor.obj T → relativeProjDegreeBaseChangeObj g F_d T :=
  relativeProjDegreeFunctorBaseChangeIsoHomAppOfEquiv
    g F_d 𝒜' F'_d comparison.pointEquiv T

/-- The raw inverse point map in the base-change comparison of degreewise relative
projective-spectrum functors. -/
def relativeProjDegreeFunctorBaseChangeIsoInvApp
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison : RelativeProjDegreeFunctorBaseChangeComparison g F_d 𝒜' F'_d)
    (T : Schemeᵒᵖ) :
    relativeProjDegreeBaseChangeObj g F_d T → F'_d.toFunctor.obj T :=
  fun x ↦
    let y : F_d.pointOver T (x.1.1 ≫ g) := ⟨x.1.2, x.2.symm⟩
    ((comparison.pointEquiv T x.1.1).symm y).1

/-- The forward raw point maps in the base-change comparison are natural in the test scheme. -/
theorem relativeProjDegreeFunctorBaseChangeIso_hom_naturality
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison : RelativeProjDegreeFunctorBaseChangeComparison g F_d 𝒜' F'_d)
    {T T' : Schemeᵒᵖ} (a : T ⟶ T') :
    F'_d.toFunctor.map a ≫
        TypeCat.ofHom (relativeProjDegreeFunctorBaseChangeIsoHomApp
          g F_d 𝒜' F'_d comparison T') =
      TypeCat.ofHom (relativeProjDegreeFunctorBaseChangeIsoHomApp
        g F_d 𝒜' F'_d comparison T) ≫
        (relativeProjDegreeBaseChangeFunctor g F_d).map a := sorry

/-- The inverse raw point maps in the base-change comparison are natural in the test scheme. -/
theorem relativeProjDegreeFunctorBaseChangeIso_inv_naturality
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison : RelativeProjDegreeFunctorBaseChangeComparison g F_d 𝒜' F'_d)
    {T T' : Schemeᵒᵖ} (a : T ⟶ T') :
    (relativeProjDegreeBaseChangeFunctor g F_d).map a ≫
        TypeCat.ofHom (relativeProjDegreeFunctorBaseChangeIsoInvApp
          g F_d 𝒜' F'_d comparison T') =
      TypeCat.ofHom (relativeProjDegreeFunctorBaseChangeIsoInvApp
        g F_d 𝒜' F'_d comparison T) ≫
        F'_d.toFunctor.map a := sorry

/-- The forward natural transformation in the base-change comparison. -/
def relativeProjDegreeFunctorBaseChangeIsoHom
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison : RelativeProjDegreeFunctorBaseChangeComparison g F_d 𝒜' F'_d) :
    F'_d.toFunctor ⟶ relativeProjDegreeBaseChangeFunctor g F_d where
  app T := TypeCat.ofHom (relativeProjDegreeFunctorBaseChangeIsoHomApp
    g F_d 𝒜' F'_d comparison T)
  naturality := fun {T} {T'} a ↦
    relativeProjDegreeFunctorBaseChangeIso_hom_naturality
      g F_d 𝒜' F'_d comparison (a : T ⟶ T')

/-- The inverse natural transformation in the base-change comparison. -/
def relativeProjDegreeFunctorBaseChangeIsoInv
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison : RelativeProjDegreeFunctorBaseChangeComparison g F_d 𝒜' F'_d) :
    relativeProjDegreeBaseChangeFunctor g F_d ⟶ F'_d.toFunctor where
  app T := TypeCat.ofHom (relativeProjDegreeFunctorBaseChangeIsoInvApp
    g F_d 𝒜' F'_d comparison T)
  naturality := fun {T} {T'} a ↦
    relativeProjDegreeFunctorBaseChangeIso_inv_naturality
      g F_d 𝒜' F'_d comparison (a : T ⟶ T')

/-- The forward and inverse base-change transformations compose to the identity on the
pulled-back functor. -/
theorem relativeProjDegreeFunctorBaseChangeIso_hom_inv_id
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison : RelativeProjDegreeFunctorBaseChangeComparison g F_d 𝒜' F'_d) :
    relativeProjDegreeFunctorBaseChangeIsoHom g F_d 𝒜' F'_d comparison ≫
        relativeProjDegreeFunctorBaseChangeIsoInv g F_d 𝒜' F'_d comparison =
      𝟙 F'_d.toFunctor := sorry

/-- The inverse and forward base-change transformations compose to the identity on the
base-changed functor. -/
theorem relativeProjDegreeFunctorBaseChangeIso_inv_hom_id
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison : RelativeProjDegreeFunctorBaseChangeComparison g F_d 𝒜' F'_d) :
    relativeProjDegreeFunctorBaseChangeIsoInv g F_d 𝒜' F'_d comparison ≫
        relativeProjDegreeFunctorBaseChangeIsoHom g F_d 𝒜' F'_d comparison =
      𝟙 (relativeProjDegreeBaseChangeFunctor g F_d) := sorry

/-- The natural isomorphism between the degreewise relative projective-spectrum functor of a
chosen pullback and the base change of the original functor. -/
def relativeProjDegreeFunctorBaseChangeIso
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison : RelativeProjDegreeFunctorBaseChangeComparison g F_d 𝒜' F'_d) :
    F'_d.toFunctor ≅ relativeProjDegreeBaseChangeFunctor g F_d where
  hom := relativeProjDegreeFunctorBaseChangeIsoHom g F_d 𝒜' F'_d comparison
  inv := relativeProjDegreeFunctorBaseChangeIsoInv g F_d 𝒜' F'_d comparison
  hom_inv_id := relativeProjDegreeFunctorBaseChangeIso_hom_inv_id g F_d 𝒜' F'_d comparison
  inv_hom_id := relativeProjDegreeFunctorBaseChangeIso_inv_hom_id g F_d 𝒜' F'_d comparison

/-- The explicit pointwise base-change type is canonically isomorphic to the
value of the categorical pullback functor. -/
noncomputable def relativeProjDegreeBaseChangeObjIsoPullback
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d) (T : Schemeᵒᵖ) :
    relativeProjDegreeBaseChangeObj g F_d T ≅
      (CategoryTheory.Limits.pullback (yoneda.map g) F_d.baseMap).obj T :=
  (CategoryTheory.Limits.pullbackObjIso (yoneda.map g) F_d.baseMap T ≪≫
    CategoryTheory.Limits.Types.pullbackIsoPullback
      ((yoneda.map g).app T) (F_d.baseMap.app T)).symm

/-- The canonical objectwise comparison with the categorical pullback is
natural in the test scheme. -/
theorem relativeProjDegreeBaseChangeObjIsoPullback_naturality
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d)
    {T T' : Schemeᵒᵖ} (a : T ⟶ T') :
    (relativeProjDegreeBaseChangeFunctor g F_d).map a ≫
        (relativeProjDegreeBaseChangeObjIsoPullback g F_d T').hom =
      (relativeProjDegreeBaseChangeObjIsoPullback g F_d T).hom ≫
        (CategoryTheory.Limits.pullback (yoneda.map g) F_d.baseMap).map a := sorry

/-- The explicit pointwise base-change functor is canonically naturally
isomorphic to the categorical pullback functor. -/
noncomputable def relativeProjDegreeBaseChangeFunctorIsoPullback
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d) :
    relativeProjDegreeBaseChangeFunctor g F_d ≅
      CategoryTheory.Limits.pullback (yoneda.map g) F_d.baseMap :=
  NatIso.ofComponents
    (fun T ↦ relativeProjDegreeBaseChangeObjIsoPullback g F_d T)
    (fun {T T'} a ↦ relativeProjDegreeBaseChangeObjIsoPullback_naturality
      g F_d (a : T ⟶ T'))

namespace RelativeProjDegreeFunctorPullback

/-- The base-change isomorphism obtained from a chosen pullback package. -/
def toBaseChangeIso
    {g : S' ⟶ S} {F_d : RelativeProjDegreeFunctor S 𝒜 d}
    (F'_d : RelativeProjDegreeFunctorPullback g F_d) :
    F'_d.toFunctor ≅ relativeProjDegreeBaseChangeFunctor g F_d :=
  relativeProjDegreeFunctorBaseChangeIso
    g F_d F'_d.algebra F'_d.toRelativeProjDegreeFunctor F'_d.toBaseChangeComparison

/-- The canonical base-change isomorphism from a chosen pullback package to
the categorical pullback of functors. -/
noncomputable def toPullbackIso
    {g : S' ⟶ S} {F_d : RelativeProjDegreeFunctor S 𝒜 d}
    (F'_d : RelativeProjDegreeFunctorPullback g F_d) :
    F'_d.toFunctor ≅
      CategoryTheory.Limits.pullback (yoneda.map g) F_d.baseMap :=
  F'_d.toBaseChangeIso ≪≫ relativeProjDegreeBaseChangeFunctorIsoPullback g F_d

end RelativeProjDegreeFunctorPullback

/-- The forward morphism of the base-change isomorphism is the named forward natural
transformation. -/
theorem relativeProjDegreeFunctorBaseChangeIso_hom
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison : RelativeProjDegreeFunctorBaseChangeComparison g F_d 𝒜' F'_d) :
    (relativeProjDegreeFunctorBaseChangeIso g F_d 𝒜' F'_d comparison).hom =
      relativeProjDegreeFunctorBaseChangeIsoHom g F_d 𝒜' F'_d comparison := sorry

/-- The inverse morphism of the base-change isomorphism is the named inverse natural
transformation. -/
theorem relativeProjDegreeFunctorBaseChangeIso_inv
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison : RelativeProjDegreeFunctorBaseChangeComparison g F_d 𝒜' F'_d) :
    (relativeProjDegreeFunctorBaseChangeIso g F_d 𝒜' F'_d comparison).inv =
      relativeProjDegreeFunctorBaseChangeIsoInv g F_d 𝒜' F'_d comparison := sorry

/-- The forward component of the base-change isomorphism evaluates to the explicit forward
point map. -/
theorem relativeProjDegreeFunctorBaseChangeIso_homApp
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison : RelativeProjDegreeFunctorBaseChangeComparison g F_d 𝒜' F'_d)
    (T : Schemeᵒᵖ) (x : F'_d.toFunctor.obj T) :
    (relativeProjDegreeFunctorBaseChangeIso g F_d 𝒜' F'_d comparison).hom.app T x =
      relativeProjDegreeFunctorBaseChangeIsoHomApp g F_d 𝒜' F'_d comparison T x := sorry

/-- The inverse component of the base-change isomorphism evaluates to the explicit inverse
point map. -/
theorem relativeProjDegreeFunctorBaseChangeIso_invApp
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : RelativeProjDegreeFunctor S' 𝒜' d)
    (comparison : RelativeProjDegreeFunctorBaseChangeComparison g F_d 𝒜' F'_d)
    (T : Schemeᵒᵖ) (x : relativeProjDegreeBaseChangeObj g F_d T) :
    (relativeProjDegreeFunctorBaseChangeIso g F_d 𝒜' F'_d comparison).inv.app T x =
      relativeProjDegreeFunctorBaseChangeIsoInvApp g F_d 𝒜' F'_d comparison T x := sorry

end AlgebraicGeometry.Scheme
