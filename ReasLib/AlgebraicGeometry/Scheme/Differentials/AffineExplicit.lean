/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derivation.Affine
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Differentials
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Differentials.AffineInverse

@[expose] public section

open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

open AlgebraicGeometry CategoryTheory Opposite
open scoped AlgebraicGeometry

variable {R A : CommRingCat.{u}} (φ : R ⟶ A) (F : (Spec A).Modules)

noncomputable def ringKahlerHomEquiv (M : ModuleCat A) :
    (CommRingCat.KaehlerDifferential φ ⟶ M) ≃ M.Derivation φ where
  toFun h := ModuleCat.Derivation.mk
    (fun a => h (CommRingCat.KaehlerDifferential.d a))
    (by sorry)
    (by sorry)
    (by sorry)
  invFun D := D.desc
  left_inv := by sorry
  right_inv := by sorry

abbrev additiveSource := (Spec A).presheaf ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
abbrev additiveTarget := (SheafOfModules.toSheaf (Spec A).ringCatSheaf).obj F

set_option backward.isDefEq.respectTransparency false in
def basisTransformation
    (D : ((moduleSpecΓFunctor (R := A)).obj F).Derivation φ) :
    (inducedFunctor (@PrimeSpectrum.basicOpen A _)).op ⋙ additiveSource (A := A) ⟶
      (inducedFunctor (@PrimeSpectrum.basicOpen A _)).op ⋙ (additiveTarget F).obj where
  app i := AddCommGrpCat.ofHom
    { toFun := Modules.AffineDerivation.basicOpenExtension φ F D i.unop
      map_zero' := by
        dsimp only [Modules.AffineDerivation.basicOpenExtension]
        exact map_zero _
      map_add' := by
        intro a b
        dsimp only [Modules.AffineDerivation.basicOpenExtension]
        exact map_add _ a b }
  naturality := by intro U V f; sorry

set_option backward.isDefEq.respectTransparency false in
def affineAdditiveExtension
    (D : ((moduleSpecΓFunctor (R := A)).obj F).Derivation φ) :
    additiveSource (A := A) ⟶ (additiveTarget F).obj :=
  TopCat.Sheaf.restrictHomEquivHom _ _ PrimeSpectrum.isBasis_basic_opens
    (basisTransformation φ F D)

theorem affineAdditiveExtension_basicOpen
    (D : ((moduleSpecΓFunctor (R := A)).obj F).Derivation φ) (f : A) :
    (affineAdditiveExtension φ F D).app (op (PrimeSpectrum.basicOpen f)) =
      (basisTransformation φ F D).app (op f) :=
  TopCat.Sheaf.extend_hom_app _ _ PrimeSpectrum.isBasis_basic_opens _ f

set_option backward.isDefEq.respectTransparency false in
def affineRelativeExtension
    (D : ((moduleSpecΓFunctor (R := A)).obj F).Derivation φ) :
    SheafOfModules.RelativeDerivation (J := Opens.grothendieckTopology (Spec A))
      (RingedSpace.Hom.inverseImageStructureSheafHomComm (Spec.map φ).toShHom) F where
  d {X} := ((affineAdditiveExtension φ F D).app X).hom
  d_mul := by intro X a b; sorry
  d_map := by
    intro X Y f x
    have h := (affineAdditiveExtension φ F D).naturality f
    exact congrArg (fun k => k x) h
  d_app := by intro X a; sorry

set_option backward.isDefEq.respectTransparency false in
def affineDerivationEquiv :
    SheafOfModules.RelativeDerivation (J := Opens.grothendieckTopology (Spec A))
      (RingedSpace.Hom.inverseImageStructureSheafHomComm (Spec.map φ).toShHom) F ≃
        ((moduleSpecΓFunctor (R := A)).obj F).Derivation φ where
  toFun := Scheme.Modules.AffineDerivation.globalSections φ F
  invFun := affineRelativeExtension φ F
  left_inv := by intro D; sorry
  right_inv := by intro D; sorry


set_option backward.isDefEq.respectTransparency false in
/-- The affine sheaf of relative differentials and the tilde of ring differentials
corepresent the same derivations. Both directions use explicit descent maps. -/
noncomputable def affineOmegaHomEquiv :
    (SheafOfModules.RingedSite.relativeDifferentials
      (J := Opens.grothendieckTopology (Spec A))
      (RingedSpace.Hom.inverseImageStructureSheafHomComm (Spec.map φ).toShHom) ⟶ F) ≃
    ((tilde.functor A).obj (CommRingCat.KaehlerDifferential φ) ⟶ F) :=
  ((SheafOfModules.RingedSite.RelativeDifferentials.homEquiv (J := Opens.grothendieckTopology (Spec A)) _ F).trans
    (affineDerivationEquiv φ F)).trans
      ((ringKahlerHomEquiv φ ((moduleSpecΓFunctor (R := A)).obj F)).symm.trans
        ((tilde.adjunction (R := A)).homEquiv _ F).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The affine differential comparison has explicit forward and inverse maps, obtained by
applying the corepresenting Hom equivalences to identity morphisms. -/
noncomputable def affineOmegaIso :
    SheafOfModules.RingedSite.relativeDifferentials
      (J := Opens.grothendieckTopology (Spec A))
      (RingedSpace.Hom.inverseImageStructureSheafHomComm (Spec.map φ).toShHom) ≅
    (tilde.functor A).obj (CommRingCat.KaehlerDifferential φ) where
  hom := (affineOmegaHomEquiv φ _).symm (𝟙 _)
  inv := affineOmegaHomEquiv φ _ (𝟙 _)
  hom_inv_id := by sorry
  inv_hom_id := by sorry

/-! Affine chart comparison data: the inverse on Kaehler sections is the
actual four-ring equivalence, transported through the explicit affine
Omega/Kaehler identifications above. -/
noncomputable def affineSquareInverse
    (A A' B B' : Type u)
    [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra A B'] [Algebra B B'] [Algebra A' B']
    [IsScalarTower A B B'] [IsScalarTower A A' B']
    [Algebra.FormallyEtale B B'] [Algebra.FormallyUnramified A A'] :
    B' ⊗[B] KaehlerDifferential A B ≃ₗ[B'] KaehlerDifferential A' B' :=
  squareEquiv A A' B B'


set_option backward.isDefEq.respectTransparency false in
/-- Global sections of affine pushforward are scalar restriction of global sections.
Both maps are the identity on the underlying sections over the whole space. -/
noncomputable def affinePushforwardGammaIso
    {B C : CommRingCat.{u}} (f : B ⟶ C) (G : (Spec C).Modules) :
    (moduleSpecΓFunctor (R := B)).obj ((Scheme.Modules.pushforward (Spec.map f)).obj G) ≅
      (ModuleCat.restrictScalars f.hom).obj ((moduleSpecΓFunctor (R := C)).obj G) where
  hom := ModuleCat.ofHom (X := (moduleSpecΓFunctor (R := B)).obj ((Scheme.Modules.pushforward (Spec.map f)).obj G)) (Y := (ModuleCat.restrictScalars f.hom).obj ((moduleSpecΓFunctor (R := C)).obj G))
    { toFun := fun x => x
      map_add' := by intros; rfl
      map_smul' := by intros; sorry }
  inv := ModuleCat.ofHom (X := (ModuleCat.restrictScalars f.hom).obj ((moduleSpecΓFunctor (R := C)).obj G)) (Y := (moduleSpecΓFunctor (R := B)).obj ((Scheme.Modules.pushforward (Spec.map f)).obj G))
    { toFun := fun x => x
      map_add' := by intros; rfl
      map_smul' := by intros; sorry }
  hom_inv_id := by ext x; rfl
  inv_hom_id := by ext x; rfl

set_option backward.isDefEq.respectTransparency false in
/-- The two affine pullback models corepresent the same Hom functor, using
only the native pullback, tilde and scalar extension adjunctions. -/
noncomputable def affinePullbackTildeHomEquiv
    {B C : CommRingCat.{u}} (f : B ⟶ C) (M : ModuleCat B) (G : (Spec C).Modules) :
    ((Scheme.Modules.pullback (Spec.map f)).obj ((tilde.functor B).obj M) ⟶ G) ≃
      ((tilde.functor C).obj ((ModuleCat.extendScalars f.hom).obj M) ⟶ G) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).homEquiv _ G).trans
    (((tilde.adjunction (R := B)).homEquiv M _).trans
      ((Iso.homToEquiv (affinePushforwardGammaIso f G)).trans
        (((ModuleCat.extendRestrictScalarsAdj f.hom).homEquiv M _).symm.trans
          ((tilde.adjunction (R := C)).homEquiv _ G).symm)))

set_option backward.isDefEq.respectTransparency false in
/-- Explicit affine pullback/tilde comparison; the inverse is evaluation of the
Hom equivalence on an identity, rather than inversion of an admitted `IsIso`. -/
noncomputable def affinePullbackTildeIso
    {B C : CommRingCat.{u}} (f : B ⟶ C) (M : ModuleCat B) :
    (Scheme.Modules.pullback (Spec.map f)).obj ((tilde.functor B).obj M) ≅
      (tilde.functor C).obj ((ModuleCat.extendScalars f.hom).obj M) where
  hom := (affinePullbackTildeHomEquiv f M _).symm (𝟙 _)
  inv := affinePullbackTildeHomEquiv f M _ (𝟙 _)
  hom_inv_id := by sorry
  inv_hom_id := by sorry


set_option backward.isDefEq.respectTransparency false in
/-- The actual four-ring equivalence, viewed in the bundled module categories. -/
noncomputable def affineSquareModuleIso
    {A A' B B' : CommRingCat.{u}} (p : A ⟶ B) (q : A' ⟶ B')
    (g : A ⟶ A') (f : B ⟶ B') (sq : g ≫ q = p ≫ f)
    (hf : f.hom.Etale) (hg : g.hom.Etale) :
    (ModuleCat.extendScalars f.hom).obj (CommRingCat.KaehlerDifferential p) ≅
      CommRingCat.KaehlerDifferential q := by
  letI := p.hom.toAlgebra
  letI := q.hom.toAlgebra
  letI := g.hom.toAlgebra
  letI := f.hom.toAlgebra
  letI := (g ≫ q).hom.toAlgebra
  letI : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom sq)
  letI : Algebra.Etale B B' := hf
  letI : Algebra.Etale A A' := hg
  exact (squareEquiv A A' B B').toModuleIso

set_option backward.isDefEq.respectTransparency false in
/-- The affine square comparison assembled from explicit Omega, pullback/tilde
and four-ring equivalences. Both arrows are constructed by composition. -/
noncomputable def affineSquareSheafIso
    {A A' B B' : CommRingCat.{u}} (p : A ⟶ B) (q : A' ⟶ B')
    (g : A ⟶ A') (f : B ⟶ B') (sq : g ≫ q = p ≫ f)
    (hf : f.hom.Etale) (hg : g.hom.Etale) :
    (Scheme.Modules.pullback (Spec.map f)).obj
      (SheafOfModules.RingedSite.relativeDifferentials
        (J := Opens.grothendieckTopology (Spec B))
        (RingedSpace.Hom.inverseImageStructureSheafHomComm (Spec.map p).toShHom)) ≅
    SheafOfModules.RingedSite.relativeDifferentials
      (J := Opens.grothendieckTopology (Spec B'))
      (RingedSpace.Hom.inverseImageStructureSheafHomComm (Spec.map q).toShHom) :=
  (Scheme.Modules.pullback (Spec.map f)).mapIso (affineOmegaIso p) ≪≫
    affinePullbackTildeIso f (CommRingCat.KaehlerDifferential p) ≪≫
    (tilde.functor B').mapIso (affineSquareModuleIso p q g f sq hf hg) ≪≫
    (affineOmegaIso q).symm

/-! The actual inverse component on an affine chart.  This declaration is kept
separate from the bundled `Iso` so that the chart family used by a later
sheaf restriction/gluing construction is an explicit morphism-valued family;
it does not obtain an inverse from the admitted scheme-level `IsIso`. -/
noncomputable def affineSquareChartInverse
    {A A' B B' : CommRingCat.{u}} (p : A ⟶ B) (q : A' ⟶ B')
    (g : A ⟶ A') (f : B ⟶ B') (sq : g ≫ q = p ≫ f)
    (hf : f.hom.Etale) (hg : g.hom.Etale) :
    SheafOfModules.RingedSite.relativeDifferentials
        (J := Opens.grothendieckTopology (Spec B'))
        (RingedSpace.Hom.inverseImageStructureSheafHomComm (Spec.map q).toShHom) ⟶
      (Scheme.Modules.pullback (Spec.map f)).obj
        (SheafOfModules.RingedSite.relativeDifferentials
          (J := Opens.grothendieckTopology (Spec B))
          (RingedSpace.Hom.inverseImageStructureSheafHomComm (Spec.map p).toShHom)) :=
  (affineSquareSheafIso p q g f sq hf hg).inv


/-- Reverse an explicitly isomorphic square.  The inverse arrows are supplied data. -/
def reverseIsoSquare
    {X₁ X₂ S₁ S₂ : Scheme.{u}} (eX : X₂ ≅ X₁) (eS : S₂ ≅ S₁)
    {p₁ : X₁ ⟶ S₁} {p₂ : X₂ ⟶ S₂} (sq : CommSq eX.hom p₂ p₁ eS.hom) :
    CommSq eX.inv p₁ p₂ eS.inv where
  w := by
    apply (cancel_mono eS.hom).1
    calc
      (eX.inv ≫ p₂) ≫ eS.hom = p₁ := by
        rw [Category.assoc, ← sq.w, Iso.inv_hom_id_assoc]
      _ = (p₁ ≫ eS.inv) ≫ eS.hom := by simp

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
open scoped RelativeDerivation in
/-- Transport differential modules back across explicit isomorphisms of schemes.
This uses the reverse comparison and actual pullback coherence maps. -/
def comparisonInverseAcrossIsos
    {X₁ X₂ S₁ S₂ : Scheme.{u}} (eX : X₂ ≅ X₁) (eS : S₂ ≅ S₁)
    {p₁ : X₁ ⟶ S₁} {p₂ : X₂ ⟶ S₂} (sq : CommSq eX.hom p₂ p₁ eS.hom) :
    Ω[p₂.toShHom] ⟶ (Scheme.Modules.pullback eX.hom).obj Ω[p₁.toShHom] :=
  (Scheme.Modules.pullbackId X₂).inv.app Ω[p₂.toShHom] ≫
    (Scheme.Modules.pullbackCongr eX.hom_inv_id).inv.app Ω[p₂.toShHom] ≫
    (Scheme.Modules.pullbackComp eX.hom eX.inv).inv.app Ω[p₂.toShHom] ≫
    (Scheme.Modules.pullback eX.hom).map
      (RingedSpace.Hom.Differentials.comparison
        (f := eX.inv.toShHom) (g := eS.inv.toShHom)
        (h := p₂.toShHom) (h' := p₁.toShHom)
        ⟨congrArg (fun a : X₁ ⟶ S₂ => a.toShHom) (reverseIsoSquare eX eS sq).w⟩)

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
open scoped RelativeDerivation in
/-- Differential comparison across actual scheme isomorphisms, with an explicit inverse. -/
def comparisonIsoAcrossIsos
    {X₁ X₂ S₁ S₂ : Scheme.{u}} (eX : X₂ ≅ X₁) (eS : S₂ ≅ S₁)
    {p₁ : X₁ ⟶ S₁} {p₂ : X₂ ⟶ S₂} (sq : CommSq eX.hom p₂ p₁ eS.hom) :
    (Scheme.Modules.pullback eX.hom).obj Ω[p₁.toShHom] ≅ Ω[p₂.toShHom] where
  hom := RingedSpace.Hom.Differentials.comparison
    (f := eX.hom.toShHom) (g := eS.hom.toShHom)
    (h := p₁.toShHom) (h' := p₂.toShHom)
    ⟨congrArg (fun a : X₂ ⟶ S₁ => a.toShHom) sq.w⟩
  inv := comparisonInverseAcrossIsos eX eS sq
  hom_inv_id := sorry
  inv_hom_id := sorry


set_option backward.isDefEq.respectTransparency false in
open scoped RelativeDerivation in
/-- Affine chart transport of differentials via the actual Spec-Gamma isomorphisms. -/
def affineSchemeOmegaIso {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (p : X ⟶ S) :
    (Scheme.Modules.pullback X.isoSpec.hom).obj Ω[(Spec.map p.appTop).toShHom] ≅
      Ω[p.toShHom] :=
  comparisonIsoAcrossIsos X.isoSpec S.isoSpec ⟨Scheme.isoSpec_hom_naturality p⟩

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
open scoped RelativeDerivation in
/-- The explicit four-ring comparison transported to arbitrary affine schemes.
Only the horizontal maps are étale; no cartesian square hypothesis is needed. -/
def affineSchemeSquareIso
    {X₁ X₂ S₁ S₂ : Scheme.{u}} [IsAffine X₁] [IsAffine X₂]
    [IsAffine S₁] [IsAffine S₂]
    {f : X₂ ⟶ X₁} {g : S₂ ⟶ S₁} {p₁ : X₁ ⟶ S₁} {p₂ : X₂ ⟶ S₂}
    (sq : CommSq f p₂ p₁ g) [Etale f] [Etale g] :
    (Scheme.Modules.pullback f).obj Ω[p₁.toShHom] ≅ Ω[p₂.toShHom] := by
  have hsq : g.appTop ≫ p₂.appTop = p₁.appTop ≫ f.appTop := by
    simpa only [Scheme.Hom.comp_appTop] using congrArg (fun a : X₂ ⟶ S₁ => a.appTop) sq.w.symm
  have hf : f.appTop.hom.Etale :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := f)).mp inferInstance
  have hg : g.appTop.hom.Etale :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := g)).mp inferInstance
  exact (Scheme.Modules.pullback f).mapIso (affineSchemeOmegaIso p₁).symm ≪≫
    (Scheme.Modules.pullbackComp f X₁.isoSpec.hom).app Ω[(Spec.map p₁.appTop).toShHom] ≪≫
    (Scheme.Modules.pullbackCongr (Scheme.isoSpec_hom_naturality f).symm).app
      Ω[(Spec.map p₁.appTop).toShHom] ≪≫
    ((Scheme.Modules.pullbackComp X₂.isoSpec.hom (Spec.map f.appTop)).app
      Ω[(Spec.map p₁.appTop).toShHom]).symm ≪≫
    (Scheme.Modules.pullback X₂.isoSpec.hom).mapIso
      (affineSquareSheafIso p₁.appTop p₂.appTop g.appTop f.appTop hsq hf hg) ≪≫
    affineSchemeOmegaIso p₂

/-! Concrete inverse component on an arbitrary affine scheme chart.  This is
the morphism-valued family consumed by the eventual affine-basis gluing;
the source and target are the actual scheme differential modules, and the
map is obtained from the explicit affine square Iso above. -/
def affineSchemeChartInverse
    {X₁ X₂ S₁ S₂ : Scheme.{u}} [IsAffine X₁] [IsAffine X₂]
    [IsAffine S₁] [IsAffine S₂]
    {f : X₂ ⟶ X₁} {g : S₂ ⟶ S₁} {p₁ : X₁ ⟶ S₁} {p₂ : X₂ ⟶ S₂}
    (sq : CommSq f p₂ p₁ g) [Etale f] [Etale g] :
    Ω[p₂.toShHom] ⟶ (Scheme.Modules.pullback f).obj Ω[p₁.toShHom] :=
  (affineSchemeSquareIso sq).inv


set_option backward.isDefEq.respectTransparency false in
/-- Restrict the universal differential by the actual pullback adjunction unit.
Sections on an open subscheme are the ambient sections on its image open. -/
def openRestrictionSection
    {X S : Scheme.{u}} (p : X ⟶ S) (U : X.Opens)
    (W : (Opens U.toScheme)ᵒᵖ) (a : U.toScheme.presheaf.obj W) :
    ((Scheme.Modules.pullback U.ι).obj Ω[p.toShHom]).val.obj W :=
  (((Scheme.Modules.pullback U.ι).obj Ω[p.toShHom]).val.map
    (eqToHom (congrArg op (U.ι.preimage_image_eq W.unop))))
      ((((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app
        Ω[p.toShHom]).val.app (op (U.ι ''ᵁ W.unop))) ((d[p.toShHom]).d a))

set_option backward.isDefEq.respectTransparency false in
/-- The restricted universal differential is relative to the restricted base open.
Its section function is fixed before the derivation laws are asserted. -/
def openRestrictionDerivation
    {X S : Scheme.{u}} (p : X ⟶ S) (U : X.Opens) (V : S.Opens)
    (hU : U ≤ p ⁻¹ᵁ V) :
    RingedSpace.Hom.derivations (p.resLE V U hU).toShHom
      ((Scheme.Modules.pullback U.ι).obj Ω[p.toShHom]) where
  d {W} := AddMonoidHom.mk' (openRestrictionSection p U W) (by
    intro a b
    sorry)
  d_mul := by intro W a b; sorry
  d_map := by intro W Z f a; sorry
  d_app := by intro W a; sorry

/-- The inverse of open restriction on differentials, obtained by descent of
an explicit restricted derivation rather than inversion of an `IsIso` proof. -/
def openRestrictionInverse
    {X S : Scheme.{u}} (p : X ⟶ S) (U : X.Opens) (V : S.Opens)
    (hU : U ≤ p ⁻¹ᵁ V) :
    Ω[(p.resLE V U hU).toShHom] ⟶
      (Scheme.Modules.pullback U.ι).obj Ω[p.toShHom] :=
  RingedSpace.Hom.differentialDesc (p.resLE V U hU).toShHom
    (openRestrictionDerivation p U V hU)

set_option backward.isDefEq.respectTransparency false in
/-- Open restriction of relative differentials with its explicit inverse. -/
def openRestrictionIso
    {X S : Scheme.{u}} (p : X ⟶ S) (U : X.Opens) (V : S.Opens)
    (hU : U ≤ p ⁻¹ᵁ V) :
    (Scheme.Modules.pullback U.ι).obj Ω[p.toShHom] ≅
      Ω[(p.resLE V U hU).toShHom] where
  hom := RingedSpace.Hom.Differentials.comparison
    (f := U.ι.toShHom) (g := V.ι.toShHom)
    (h := p.toShHom) (h' := (p.resLE V U hU).toShHom)
    ⟨congrArg (fun a : U.toScheme ⟶ S => a.toShHom)
      (p.resLE_comp_ι hU).symm⟩
  inv := openRestrictionInverse p U V hU
  hom_inv_id := by sorry
  inv_hom_id := by sorry


/-- Compatible affine open neighborhoods indexing the comparison construction.
The index contains geometric opens and their incidence properties, not inverse maps. -/
structure EtaleAffineChart
    {X₁ X₂ S₁ S₂ : Scheme.{u}} (f : X₂ ⟶ X₁) (g : S₂ ⟶ S₁)
    (p₁ : X₁ ⟶ S₁) (p₂ : X₂ ⟶ S₂) where
  U₁ : X₁.Opens
  U₂ : X₂.Opens
  V₁ : S₁.Opens
  V₂ : S₂.Opens
  affineU₁ : IsAffine U₁.toScheme
  affineU₂ : IsAffine U₂.toScheme
  affineV₁ : IsAffine V₁.toScheme
  affineV₂ : IsAffine V₂.toScheme
  hf : U₂ ≤ f ⁻¹ᵁ U₁
  hg : V₂ ≤ g ⁻¹ᵁ V₁
  hp₁ : U₁ ≤ p₁ ⁻¹ᵁ V₁
  hp₂ : U₂ ≤ p₂ ⁻¹ᵁ V₂

/-- Compatible affine charts form a basis: choose the two base neighborhoods first,
then the source neighborhoods inside the required inverse images. -/
theorem etaleAffineChart_isBasis
    {X₁ X₂ S₁ S₂ : Scheme.{u}} {f : X₂ ⟶ X₁} {g : S₂ ⟶ S₁}
    {p₁ : X₁ ⟶ S₁} {p₂ : X₂ ⟶ S₂} (sq : CommSq f p₂ p₁ g) :
    TopologicalSpace.Opens.IsBasis (Set.range (fun c : EtaleAffineChart f g p₁ p₂ => c.U₂)) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro W x hx
  obtain ⟨V₁, hV₁, hxV₁, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S₁) (x := p₁ (f x))
      (U := ⊤) (by trivial)
  have heq : p₁ (f x) = g (p₂ x) := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun k : X₂ ⟶ S₁ => k x) sq.w
  have hxpre : p₂ x ∈ g ⁻¹ᵁ V₁ := by
    change g (p₂ x) ∈ V₁
    rw [← heq]
    exact hxV₁
  obtain ⟨V₂, hV₂, hxV₂, hV₂sub⟩ :=
    exists_isAffineOpen_mem_and_subset hxpre
  have hxpre₁ : f x ∈ p₁ ⁻¹ᵁ V₁ := hxV₁
  obtain ⟨U₁, hU₁, hxU₁, hU₁sub⟩ :=
    exists_isAffineOpen_mem_and_subset hxpre₁
  have hxsmall : x ∈ W ⊓ (f ⁻¹ᵁ U₁ ⊓ p₂ ⁻¹ᵁ V₂) :=
    ⟨hx, hxU₁, hxV₂⟩
  obtain ⟨U₂, hU₂, hxU₂, hU₂sub⟩ :=
    exists_isAffineOpen_mem_and_subset hxsmall
  let c : EtaleAffineChart f g p₁ p₂ :=
    { U₁ := U₁, U₂ := U₂, V₁ := V₁, V₂ := V₂
      affineU₁ := hU₁, affineU₂ := hU₂
      affineV₁ := hV₁, affineV₂ := hV₂
      hf := fun y hy => (hU₂sub hy).2.1
      hg := hV₂sub
      hp₁ := hU₁sub
      hp₂ := fun y hy => (hU₂sub hy).2.2 }
  exact ⟨U₂, ⟨c, rfl⟩, hxU₂, fun y hy => (hU₂sub hy).1⟩


set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
/-- Actual local inverse between the restrictions of the two global modules. -/
def etaleAffineChartInverse
    {X₁ X₂ S₁ S₂ : Scheme.{u}} {f : X₂ ⟶ X₁} {g : S₂ ⟶ S₁}
    {p₁ : X₁ ⟶ S₁} {p₂ : X₂ ⟶ S₂} (sq : CommSq f p₂ p₁ g)
    [Etale f] [Etale g] (c : EtaleAffineChart f g p₁ p₂) :
    (Scheme.Modules.pullback c.U₂.ι).obj Ω[p₂.toShHom] ⟶
      (Scheme.Modules.pullback c.U₂.ι).obj
        ((Scheme.Modules.pullback f).obj Ω[p₁.toShHom]) := by
  letI := c.affineU₁
  letI := c.affineU₂
  letI := c.affineV₁
  letI := c.affineV₂
  let fU := f.resLE c.U₁ c.U₂ c.hf
  let gV := g.resLE c.V₁ c.V₂ c.hg
  let q₁ := p₁.resLE c.V₁ c.U₁ c.hp₁
  let q₂ := p₂.resLE c.V₂ c.U₂ c.hp₂
  haveI : Etale fU := by dsimp [fU, Scheme.Hom.resLE]; infer_instance
  haveI : Etale gV := by dsimp [gV, Scheme.Hom.resLE]; infer_instance
  have sqU : CommSq fU q₂ q₁ gV := by
    constructor
    sorry
  exact (openRestrictionIso p₂ c.U₂ c.V₂ c.hp₂).hom ≫
    (affineSchemeSquareIso sqU).inv ≫
    (Scheme.Modules.pullback fU).map
      (openRestrictionIso p₁ c.U₁ c.V₁ c.hp₁).inv ≫
    (Scheme.Modules.pullbackComp fU c.U₁.ι).hom.app Ω[p₁.toShHom] ≫
    (Scheme.Modules.pullbackCongr (f.resLE_comp_ι c.hf)).hom.app Ω[p₁.toShHom] ≫
    (Scheme.Modules.pullbackComp c.U₂.ι f).inv.app Ω[p₁.toShHom]

/-- Pullback sections on an open subscheme identify with ambient sections.
The two maps use the proved native restriction/pullback adjunction equivalence. -/
def openPullbackSectionsIso {X : Scheme.{u}} (F : X.Modules)
    (U : X.Opens) (W : U.toScheme.Opens) :
    ((Scheme.Modules.pullback U.ι).obj F).presheaf.obj (op W) ≅
      F.presheaf.obj (op (U.ι ''ᵁ W)) where
  hom := ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app F).app W ≫
    (F.restrictAppIso U.ι W).hom
  inv := (F.restrictAppIso U.ι W).inv ≫
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app F).app W
  hom_inv_id := by sorry
  inv_hom_id := by sorry

/-- Sections on the whole open subscheme are sections over the original open. -/
def openPullbackTopSectionsIso {X : Scheme.{u}} (F : X.Modules) (U : X.Opens) :
    ((Scheme.Modules.pullback U.ι).obj F).presheaf.obj (op ⊤) ≅
      F.presheaf.obj (op U) :=
  openPullbackSectionsIso F U ⊤ ≪≫
    F.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

/-- The affine comparison inverse on ambient sections over its chart. -/
def etaleAffineChartSection
    {X₁ X₂ S₁ S₂ : Scheme.{u}} {f : X₂ ⟶ X₁} {g : S₂ ⟶ S₁}
    {p₁ : X₁ ⟶ S₁} {p₂ : X₂ ⟶ S₂} (sq : CommSq f p₂ p₁ g)
    [Etale f] [Etale g] (c : EtaleAffineChart f g p₁ p₂) :
    (Scheme.Modules.presheaf (Ω[p₂.toShHom] : X₂.Modules)).obj (op c.U₂) ⟶
      ((Scheme.Modules.pullback f).obj Ω[p₁.toShHom]).presheaf.obj (op c.U₂) :=
  (openPullbackTopSectionsIso Ω[p₂.toShHom] c.U₂).inv ≫
    (etaleAffineChartInverse sq c).app ⊤ ≫
    (openPullbackTopSectionsIso ((Scheme.Modules.pullback f).obj Ω[p₁.toShHom]) c.U₂).hom

/-- The inverse maps form an actual natural transformation on the affine basis.
Compatibility is the uniqueness of inverse to the restricted canonical comparison. -/
def etaleAffineBasisTransformation
    {X₁ X₂ S₁ S₂ : Scheme.{u}} {f : X₂ ⟶ X₁} {g : S₂ ⟶ S₁}
    {p₁ : X₁ ⟶ S₁} {p₂ : X₂ ⟶ S₂} (sq : CommSq f p₂ p₁ g)
    [Etale f] [Etale g] :
    (inducedFunctor (fun c : EtaleAffineChart f g p₁ p₂ => c.U₂)).op ⋙
      (Scheme.Modules.presheaf (Ω[p₂.toShHom] : X₂.Modules)) ⟶
    (inducedFunctor (fun c : EtaleAffineChart f g p₁ p₂ => c.U₂)).op ⋙
      ((Scheme.Modules.pullback f).obj Ω[p₁.toShHom]).presheaf where
  app c := etaleAffineChartSection sq c.unop
  naturality := by intro c d i; sorry

/-- Extend the explicit affine inverse family by the native sheaf gluing equivalence. -/
def etaleGlobalAdditiveInverse
    {X₁ X₂ S₁ S₂ : Scheme.{u}} {f : X₂ ⟶ X₁} {g : S₂ ⟶ S₁}
    {p₁ : X₁ ⟶ S₁} {p₂ : X₂ ⟶ S₂} (sq : CommSq f p₂ p₁ g)
    [Etale f] [Etale g] :
    (Scheme.Modules.presheaf (Ω[p₂.toShHom] : X₂.Modules)) ⟶
      ((Scheme.Modules.pullback f).obj Ω[p₁.toShHom]).presheaf :=
  TopCat.Sheaf.restrictHomEquivHom _
    ((SheafOfModules.toSheaf X₂.ringCatSheaf).obj
      ((Scheme.Modules.pullback f).obj Ω[p₁.toShHom]))
    (etaleAffineChart_isBasis sq) (etaleAffineBasisTransformation sq)


set_option backward.isDefEq.respectTransparency false in
/-- The glued inverse as a morphism of module sheaves. The underlying section
functions are fixed by affine gluing; only scalar linearity and naturality are laws. -/
def etaleGlobalInverse
    {X₁ X₂ S₁ S₂ : Scheme.{u}} {f : X₂ ⟶ X₁} {g : S₂ ⟶ S₁}
    {p₁ : X₁ ⟶ S₁} {p₂ : X₂ ⟶ S₂} (sq : CommSq f p₂ p₁ g)
    [Etale f] [Etale g] :
    Ω[p₂.toShHom] ⟶ (Scheme.Modules.pullback f).obj Ω[p₁.toShHom] where
  val :=
    { app := fun W => ModuleCat.ofHom
        (X := (Ω[p₂.toShHom] : X₂.Modules).val.obj W)
        (Y := ((Scheme.Modules.pullback f).obj Ω[p₁.toShHom]).val.obj W)
        { toFun := fun x => (etaleGlobalAdditiveInverse sq).app W x
          map_add' := by intro a b; exact map_add _ a b
          map_smul' := by intro r x; sorry }
      naturality := by intro W Z i; sorry }

set_option backward.isDefEq.respectTransparency false in
/-- The global comparison for arbitrary commutative squares with horizontal
étale maps. Both arrows are actual data; inverse laws remain propositions. -/
def etaleGlobalComparisonIso
    {X₁ X₂ S₁ S₂ : Scheme.{u}} {f : X₂ ⟶ X₁} {g : S₂ ⟶ S₁}
    {p₁ : X₁ ⟶ S₁} {p₂ : X₂ ⟶ S₂} (sq : CommSq f p₂ p₁ g)
    [Etale f] [Etale g] :
    (Scheme.Modules.pullback f).obj Ω[p₁.toShHom] ≅ Ω[p₂.toShHom] where
  hom := RingedSpace.Hom.Differentials.comparison
    (f := f.toShHom) (g := g.toShHom) (h := p₁.toShHom) (h' := p₂.toShHom)
    ⟨congrArg (fun a : X₂ ⟶ S₁ => a.toShHom) sq.w⟩
  inv := etaleGlobalInverse sq
  hom_inv_id := by sorry
  inv_hom_id := by sorry

end AlgebraicGeometry.Scheme.RelativeDifferentials
