/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Henselization
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Acyclicity
public import ReasLib.CategoryTheory.Sites.HigherDirectImage
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (s : GeometricPoint S)
variable (Rsh : Type u) [CommRing Rsh]
variable [Algebra (S.presheaf.stalk s.image) Rsh]
variable [IsStrictHenselizationOf (S.presheaf.stalk s.image) Rsh]

/-- Base change to a chosen intrinsic strict henselization of the Zariski stalk.
To compare with the stalk at the specified geometric point, a compatible model
identification with `etaleLocalRing S s` must also be supplied. -/
abbrev henselizedFiber : Scheme.{u} :=
  pullback f (strictHenselizationMap S s Rsh)

/-- The henselized fibre is the chosen fibre product of `f` with the
strict-henselization map. -/
theorem henselizedFiber_def :
    henselizedFiber f s Rsh = pullback f (strictHenselizationMap S s Rsh) :=
  rfl

/-- The projection `p : X ×_S Spec(Rsh) ⟶ X` of the henselized fibre. -/
def henselizedFiberToX : henselizedFiber f s Rsh ⟶ X :=
  pullback.fst f (strictHenselizationMap S s Rsh)

/-- The projection is the first projection of the chosen fibre product. -/
theorem henselizedFiberToX_def :
    henselizedFiberToX f s Rsh = pullback.fst f (strictHenselizationMap S s Rsh) :=
  rfl

/-- A supplied algebra identification with the actual étale stalk induces an
identification of spectra. Both directions come from the supplied equivalence;
no isomorphism is selected from an existence statement. -/
def henselizationModelSchemeIso
    (model : etaleLocalRing S s ≃ₐ[S.presheaf.stalk s.image] Rsh) :
    strictHenselizationScheme S s Rsh ≅
      strictHenselizationScheme S s (etaleLocalRing S s) :=
  Scheme.Spec.mapIso model.toRingEquiv.toCommRingCatIso.op

/-- The model identification respects the structural maps to the base scheme. -/
theorem henselizationModelSchemeIso_over
    (model : etaleLocalRing S s ≃ₐ[S.presheaf.stalk s.image] Rsh) :
    (henselizationModelSchemeIso s Rsh model).hom ≫
        strictHenselizationMap S s (etaleLocalRing S s) =
      strictHenselizationMap S s Rsh := by
  change Spec.map (CommRingCat.ofHom model.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s.image) (etaleLocalRing S s))) ≫
        S.fromSpecStalk s.image) = _
  rw [← Spec.map_comp_assoc]
  congr 1
  congr 1
  ext a
  exact model.commutes a

set_option backward.isDefEq.respectTransparency false in
/-- Transport from a compatible strict-henselization model to the fiber formed
using the actual étale stalk of the specified geometric point. -/
def henselizedFiberModelIso
    (model : etaleLocalRing S s ≃ₐ[S.presheaf.stalk s.image] Rsh) :
    henselizedFiber f s Rsh ≅ henselizedFiber f s (etaleLocalRing S s) where
  hom := pullback.map _ _ _ _ (𝟙 X)
    (henselizationModelSchemeIso s Rsh model).hom (𝟙 S)
    (by simp) (by simpa using (henselizationModelSchemeIso_over s Rsh model).symm)
  inv := pullback.map _ _ _ _ (𝟙 X)
    (henselizationModelSchemeIso s Rsh model).inv (𝟙 S)
    (by simp) (by
      simpa using
        ((henselizationModelSchemeIso s Rsh model).inv_comp_eq.mpr
          (henselizationModelSchemeIso_over s Rsh model).symm).symm)
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

/-- Compatible model transport preserves the projection to the original scheme. -/
@[reassoc (attr := simp)]
theorem henselizedFiberModelIso_hom_toX
    (model : etaleLocalRing S s ≃ₐ[S.presheaf.stalk s.image] Rsh) :
    (henselizedFiberModelIso f s Rsh model).hom ≫
        henselizedFiberToX f s (etaleLocalRing S s) =
      henselizedFiberToX f s Rsh := by
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasExt (Sheaf (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [Abelian (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
variable [Abelian (Sheaf (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u})]
variable [EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf (henselizedFiber f s Rsh).smallEtaleTopology
    AddCommGrpCat.{u})]
variable [HasDerivedCategory AddCommGrpCat.{u}]
variable [(etaleAbelianPushforward f).Additive]
variable [((smallEtalePullback (henselizedFiberToX f s Rsh)).sheafPushforwardContinuous
    AddCommGrpCat.{u} X.smallEtaleTopology
    (henselizedFiber f s Rsh).smallEtaleTopology).IsRightAdjoint]
variable [((smallEtalePullback (henselizedFiberToX f s Rsh)).sheafPullback AddCommGrpCat.{u}
    X.smallEtaleTopology (henselizedFiber f s Rsh).smallEtaleTopology).Additive]
variable [PreservesFiniteLimits
    ((smallEtalePullback (henselizedFiberToX f s Rsh)).sheafPullback AddCommGrpCat.{u}
      X.smallEtaleTopology (henselizedFiber f s Rsh).smallEtaleTopology)]
variable [PreservesFiniteColimits
    ((smallEtalePullback (henselizedFiberToX f s Rsh)).sheafPullback AddCommGrpCat.{u}
      X.smallEtaleTopology (henselizedFiber f s Rsh).smallEtaleTopology)]
variable [(sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u} ⋙
    s.toSmallEtalePoint.presheafFiber).Additive]
variable [PreservesFiniteLimits
    (sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u} ⋙
      s.toSmallEtalePoint.presheafFiber)]
variable [PreservesFiniteColimits
    (sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u} ⋙
      s.toSmallEtalePoint.presheafFiber)]
variable [IsGrothendieckAbelian
    (Sheaf (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u})]
variable [(siteAbelianSectionsFunctor (henselizedFiber f s Rsh).smallEtaleTopology
    (globalEtale (henselizedFiber f s Rsh))).Additive]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (siteAbelianSectionsFunctor (henselizedFiber f s Rsh).smallEtaleTopology
        (globalEtale (henselizedFiber f s Rsh))))
    (HomologicalComplex.quasiIso
      (Sheaf (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u})
      (ComplexShape.up ℤ))]

/-- Inverse image of an abelian étale sheaf along the henselized-fibre projection. -/
def henselizedSheafPullback
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Sheaf (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u} :=
  ((smallEtalePullback (henselizedFiberToX f s Rsh)).sheafPullback
    AddCommGrpCat.{u} X.smallEtaleTopology
    (henselizedFiber f s Rsh).smallEtaleTopology).obj F

/-- Derived inverse image of an object of `D(X_étale)` along the henselized-fibre projection. -/
noncomputable def henselizedDerivedPullback
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    DerivedCategory
      (Sheaf (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u}) :=
  ((smallEtalePullback (henselizedFiberToX f s Rsh)).sheafPullback
    AddCommGrpCat.{u} X.smallEtaleTopology
    (henselizedFiber f s Rsh).smallEtaleTopology).mapDerivedCategory.obj K

/-- Derived étale global sections on the henselized fibre. -/
noncomputable def henselizedDerivedGlobalSections :
    DerivedCategory
      (Sheaf (henselizedFiber f s Rsh).smallEtaleTopology AddCommGrpCat.{u}) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  RightDerived.Cochain.functor
    (siteAbelianSectionsFunctor (henselizedFiber f s Rsh).smallEtaleTopology
      (globalEtale (henselizedFiber f s Rsh)))

/-- For a quasi-compact quasi-separated scheme morphism, the geometric stalk of a
higher direct image of an abelian étale sheaf is isomorphic to étale cohomology
of its inverse image on the strict-henselized fibre. -/
theorem higherDirectImage_stalk_eq_etaleCohomology
    (_model : etaleLocalRing S s ≃ₐ[S.presheaf.stalk s.image] Rsh)
    [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    IsIsomorphic
      (s.toSmallEtalePoint.sheafFiber.obj
        (Sheaf.higherDirectImage (smallEtalePullback f) F n))
      ((henselizedSheafPullback f s Rsh F).H'
        n (globalEtale (henselizedFiber f s Rsh))) := sorry

/-- For a quasi-compact quasi-separated scheme morphism and a bounded-below
derived étale sheaf, the geometric stalk of the degree-`n` derived direct image
is isomorphic to degree-`n` étale cohomology of its inverse image on the
strict-henselized fibre. -/
theorem derivedHigherDirectImage_stalk_eq_etaleCohomology
    (_model : etaleLocalRing S s ≃ₐ[S.presheaf.stalk s.image] Rsh)
    [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (n : ℤ) :
    IsIsomorphic
      (s.toSmallEtalePoint.sheafFiber.obj
        ((DerivedCategory.homologyFunctor
            (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) n).obj
          (DerivedCategory.Plus.ι.obj
            ((etaleAbelianPushforward f).rightDerivedFunctorPlus.obj K))))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((henselizedDerivedGlobalSections f s Rsh).obj
          (henselizedDerivedPullback f s Rsh (DerivedCategory.Plus.ι.obj K)))) := sorry

/-- For a quasi-compact quasi-separated scheme morphism and a bounded-below
derived étale sheaf, the derived geometric stalk of its derived direct image is
isomorphic to derived étale global sections of its inverse image on the
strict-henselized fibre, viewed in the ambient derived category. -/
theorem derivedPushforward_stalk_eq_derivedGlobalSections
    (_model : etaleLocalRing S s ≃ₐ[S.presheaf.stalk s.image] Rsh)
    [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    IsIsomorphic
      ((sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u} ⋙
          s.toSmallEtalePoint.presheafFiber).mapDerivedCategory.obj
        (DerivedCategory.Plus.ι.obj
          ((etaleAbelianPushforward f).rightDerivedFunctorPlus.obj K)))
      ((henselizedDerivedGlobalSections f s Rsh).obj
        (henselizedDerivedPullback f s Rsh (DerivedCategory.Plus.ι.obj K))) := sorry

end AlgebraicGeometry.Scheme.Etale

end
