/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Connection.DeRham
public import ReasLib.CategoryTheory.Sites.Derived.GlobalSectionsRestriction
public import ReasLib.AlgebraicGeometry.Crystalline.DeRham
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.Grp.Ulift
public import ReasLib.Algebra.Homology.Embedding.Functor

/-! # Derived restriction of crystalline de Rham complexes -/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf CrystallineModuleSheaf.CrisModuleSheaf
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry
open TopologicalSpace

universe u uC vC

namespace AlgebraicGeometry.Scheme.Crystalline

private instance liftPreservesZero {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C) :
    (sheafCompose J AddCommGrpCat.uliftFunctor.{u + 1, u}).PreservesZeroMorphisms where
  map_zero := by intros; ext U x; rfl

set_option backward.privateInPublic true in
private def liftComplex {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C)
    (K : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℕ) :
    CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℕ where
  X i := (sheafCompose J AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (K.X i)
  d i j := (sheafCompose J AddCommGrpCat.uliftFunctor.{u + 1, u}).map (K.d i j)
  shape i j h := by
    rw [K.shape i j h]
    ext U x
    rfl
  d_comp_d' i j k _ _ := by
    rw [← Functor.map_comp, K.d_comp_d]
    ext U x
    rfl

private theorem dividedPowersEquivMorphism {R R' : Type*} [CommRing R] [CommRing R']
    {J : Ideal R} {J' : Ideal R'} {e : R ≃+* R'} (h : J.map e = J')
    (δ : DividedPowers J) : δ.IsDPMorphism (DividedPowers.ofRingEquiv h δ) e.toRingHom := by
  refine ⟨le_of_eq h, ?_⟩
  intro n a ha
  exact DividedPowers.ofRingEquiv_dpow_apply h δ

private theorem quasiCompactOfClosed {A B : Scheme.{u}} (f : A ⟶ B)
    [IsClosedImmersion f] : QuasiCompact f := inferInstance

variable {S : Scheme.{u}} {I : S.IdealSheafData}
variable {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible : ∀ (V : S.affineOpens) (f : Γ(S, V)),
  (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
    (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
variable (p : ℕ) [Fact (Nat.Prime p)]
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (F : CrisModuleSheaf S I γ h_compatible X x₀) [IsCrystal F]

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
private def openInclusion (T : smallCrystallineSite S I γ h_compatible X x₀)
    (U : T.obj.1.thickening.Opens) : (smallOpensFunctor T).obj U ⟶ T :=
  ObjectProperty.homMk
    { source := Over.homMk (T.obj.1.inclusion ⁻¹ᵁ U).ι rfl
      thickening := U.ι
      source_comm := (morphismRestrict_ι T.obj.1.inclusion U).symm
      base_comm := rfl
      ideal_compatible := by
        change T.obj.1.ideal.comap U.ι ≤ (T.obj.1.inclusion ∣_ U).ker
        rw [← Scheme.IdealSheafData.le_map_iff_comap_le,
          Scheme.IdealSheafData.map_ker, morphismRestrict_ι,
          T.obj.1.ideal_eq_ker]
        exact Scheme.Hom.le_ker_comp _ _
      dividedPowers_compatible := by
        intro V W h
        change U.toScheme.affineOpens at W
        have h' : U.ι ''ᵁ W.1 ≤ V.1 := by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := hx
          exact h hy
        have H := (CrystallineObject.Hom.id T.obj.1).dividedPowers_compatible
          V ⟨U.ι ''ᵁ W.1, W.2.image_of_isOpenImmersion (Scheme.Opens.ι U)⟩ h'
        let e := (U.ι.appIso W.1).commRingCatIsoToRingEquiv
        have hIdeal :
            (T.obj.1.ideal.ideal ⟨U.ι ''ᵁ W.1,
              W.2.image_of_isOpenImmersion (Scheme.Opens.ι U)⟩).map e.toRingHom =
              (T.obj.1.inclusion ∣_ U).ker.ideal W := by
          have hqc : QuasiCompact T.obj.1.inclusion :=
            @quasiCompactOfClosed _ _ _
              T.obj.1.inclusion_isThickening.toIsClosedImmersion
          rw [T.obj.1.ideal_eq_ker,
            @Scheme.ker_morphismRestrict_ideal _ _ T.obj.1.inclusion hqc]
          simp [e]
        have he : (T.obj.1.gamma ⟨U.ι ''ᵁ W.1,
            W.2.image_of_isOpenImmersion (Scheme.Opens.ι U)⟩).IsDPMorphism
            (((smallOpensFunctor T).obj U).obj.1.gamma W) e.toRingHom := by
          change (T.obj.1.gamma _).IsDPMorphism
            ((CrystallineObject.restrictOpen T.obj.1 U).gamma W) _
          exact dividedPowersEquivMorphism hIdeal _
        convert DividedPowers.IsDPMorphism.comp _ he H using 1
        ext a
        simp only [RingHom.comp_apply, e]
        change (U.ι.appLE V W.1 h).hom a = (U.ι.appIso W.1).hom.hom
          ((Scheme.Hom.appLE (𝟙 T.obj.1.thickening) V (U.ι ''ᵁ W.1) h').hom a)
        rw [← CommRingCat.comp_apply]
        apply congrArg (fun g : Γ(T.obj.1.thickening, V.1) ⟶ Γ(U.toScheme, W.1) => g.hom a)
        rw [Scheme.Hom.appIso_hom']
        simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
        change U.ι.appLE V W.1 h = T.obj.1.thickening.presheaf.map (homOfLE h').op ≫
          U.ι.appLE (U.ι ''ᵁ W.1) W.1 _
        simp only [Scheme.Opens.ι_appLE]
        rw [← T.obj.1.thickening.presheaf.map_comp]
        rfl }


/-- Restriction to open thickenings is continuous for the crystalline and Zariski topologies. -/
instance smallOpensFunctor_isContinuous
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (smallOpensFunctor T).IsContinuous
      (Opens.grothendieckTopology T.obj.1.thickening)
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) := sorry

/-- Restriction to open thickenings is cocontinuous for the crystalline and Zariski topologies. -/
instance smallOpensFunctor_isCocontinuous
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (smallOpensFunctor T).IsCocontinuous
      (Opens.grothendieckTopology T.obj.1.thickening)
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) := sorry

variable [HasSheafify
  (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
variable [HasSheafify
  (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u + 1}]

/-- The underlying abelian coefficient sheaf, lifted in universe and placed in degree zero. -/
def crystalCoefficientDerived :
    DerivedCategory (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      AddCommGrpCat.{u + 1}) :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
      (toAbelianSheaf p S I γ h_compatible s X x₀ h_p F))

-- The coefficient-lifting implementation remains private; its public values are
-- the canonical sheaf complexes and their localizations.
set_option backward.privateInPublic true in
/-- The full crystalline de Rham complex, with lifted abelian coefficients,
extended by zero to integer degrees and localized in the derived category. -/
def crystalDeRhamDerived :
    DerivedCategory (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      AddCommGrpCat.{u + 1}) :=
  DerivedCategory.Q.obj
    ((liftComplex _ (crystalDeRhamComplex p s h_p F)).extend ComplexShape.embeddingUpNat)

/-- The full complex of sheaves on a crystalline thickening associated to the
canonical divided-power integrable connection of a crystal. -/
def crystalDeRhamOnT (T : smallCrystallineSite S I γ h_compatible X x₀) :=
  SheafOfModules.RingedSite.Connection.deRhamComplex.{u, u}
    (canonicalConnection F T) (exteriorCalculus T) (canonicalConnection_isIntegrable F T)

set_option backward.privateInPublic true in
private def localAbelianComplex (T : smallCrystallineSite S I γ h_compatible X x₀) :
    CochainComplex (Sheaf (Opens.grothendieckTopology T.obj.1.thickening)
      AddCommGrpCat.{u}) ℕ :=
  ((SheafOfModules.toSheaf (ringSheaf.{u, u, u} (Opens.grothendieckTopology T.obj.1.thickening)
    (RingedSpace.DeRham.coefficients (X := T.obj.1.thickening.toRingedSpace)
      (S := S.toRingedSpace) T.obj.1.thickeningToBase.toShHom))).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (crystalDeRhamOnT F T)

set_option backward.privateInPublic true in
/-- The local divided-power connection complex, with lifted abelian coefficients,
extended by zero and localized in the derived category of sheaves on the thickening. -/
def crystalDeRhamOnTDerived (T : smallCrystallineSite S I γ h_compatible X x₀)
    [HasSheafify (Opens.grothendieckTopology T.obj.1.thickening) AddCommGrpCat.{u + 1}] :
    DerivedCategory.{u + 2} (Sheaf (Opens.grothendieckTopology T.obj.1.thickening)
      AddCommGrpCat.{u + 1}) :=
  (DerivedCategory.Q.{u + 2, u + 1, u + 2}).obj
    ((liftComplex.{u, u, u} _ (localAbelianComplex F T)).extend ComplexShape.embeddingUpNat)

set_option backward.privateInPublic true in
private def localSectionsComparison
    (G : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) (U : T.obj.1.thickening.Opens) :
    (Scheme.Modules.presheaf (G.obj T)).obj (op U) ⟶
      abelianGlobalSections (G.obj ((smallOpensFunctor T).obj U)) :=
  Scheme.Modules.Hom.app
      (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).homEquiv _ _)
        (G.comparison (openInclusion T U))) U ≫
    eqToHom (by
      change (Scheme.Modules.presheaf ((Scheme.Modules.pushforward U.ι).obj
        (G.obj ((smallOpensFunctor T).obj U)))).obj (op U) = _
      simp only [Scheme.Modules.pushforward_obj_obj, Scheme.Opens.ι_preimage_self]
      rfl)

set_option backward.privateInPublic true in
private def localComparisonApp
    (T : smallCrystallineSite S I γ h_compatible X x₀) (i : ℕ)
    (U : (Opens T.obj.1.thickening)ᵒᵖ) :
    ((localAbelianComplex F T).X i).obj.obj U ⟶
      (crystalDeRhamTerm p s h_p F i).obj.obj ((smallOpensFunctor T).op.obj U) :=
  by
    cases i with
    | zero =>
      exact localSectionsComparison F T U.unop ≫
        (toSheafify (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
          (crystalDeRhamTermPresheaf F 0)).app ((smallOpensFunctor T).op.obj U)
    | succ n =>
      exact localSectionsComparison (crystallineTensor F (dividedPowerOmegaPower (n + 1)))
        T U.unop ≫
        (toSheafify (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
          (crystalDeRhamTermPresheaf F (n + 1))).app ((smallOpensFunctor T).op.obj U)

set_option backward.privateInPublic true in
/-- The openwise comparison induced by crystalline module and divided-power form
pullback and the sheafification unit commutes with restrictions of opens. -/
theorem crystallineDeRhamLocalComparison_naturality
    (T : smallCrystallineSite S I γ h_compatible X x₀) (i : ℕ)
    {U V : (Opens T.obj.1.thickening)ᵒᵖ} (f : U ⟶ V) :
    ((localAbelianComplex F T).X i).obj.map f ≫ localComparisonApp p s h_p F T i V =
      localComparisonApp p s h_p F T i U ≫
        (crystalDeRhamTerm p s h_p F i).obj.map ((smallOpensFunctor T).op.map f) := sorry

set_option backward.privateInPublic true in
private def localComparisonTerm
    (T : smallCrystallineSite S I γ h_compatible X x₀) (i : ℕ) :
    (localAbelianComplex F T).X i ⟶
      ((smallOpensFunctor T).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology T.obj.1.thickening)
        (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)).obj
          (crystalDeRhamTerm p s h_p F i) :=
  ⟨{ app := localComparisonApp p s h_p F T i
     naturality := fun {U V} f => crystallineDeRhamLocalComparison_naturality p s h_p F T i f }⟩

set_option backward.privateInPublic true in
/-- The canonical local comparison intertwines the connection differentials with
the restricted crystalline de Rham differentials. -/
theorem crystallineDeRhamLocalComparison_comm
    (T : smallCrystallineSite S I γ h_compatible X x₀) (i j : ℕ) :
    (localAbelianComplex F T).d i j ≫ localComparisonTerm p s h_p F T j =
      localComparisonTerm p s h_p F T i ≫
        ((smallOpensFunctor T).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology T.obj.1.thickening)
          (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)).map
            ((crystalDeRhamComplex p s h_p F).d i j) := sorry

set_option backward.privateInPublic true in
/-- The chain map from the local divided-power connection complex to the
restriction of the crystalline de Rham complex. -/
def crystallineDeRhamLocalComparison
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    localAbelianComplex F T ⟶
      (((smallOpensFunctor T).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology T.obj.1.thickening)
        (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (crystalDeRhamComplex p s h_p F) where
  f := localComparisonTerm p s h_p F T
  comm' i j _ := (crystallineDeRhamLocalComparison_comm p s h_p F T i j).symm

set_option backward.privateInPublic true in
private def liftedTruncation :
    liftComplex _ (crystalDeRhamComplex p s h_p F) ⟶
      (HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj
        ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
          (toAbelianSheaf p S I γ h_compatible s X x₀ h_p F)) :=
  ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (crystalDeRhamTruncation p s h_p F) ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1, u}) (ComplexShape.up ℕ) 0).hom.app _

set_option backward.privateInPublic true in
/-- The derived global-sections comparison from the full crystalline de Rham
complex to its degree-zero coefficient sheaf, induced by truncation. -/
def crystallineDeRhamComparison :
    (siteAbelianGlobalSectionsDerived _).obj (crystalDeRhamDerived p s h_p F) ⟶
      (siteAbelianGlobalSectionsDerived _).obj (crystalCoefficientDerived p s h_p F) :=
  (siteAbelianGlobalSectionsDerived _).map
    (DerivedCategory.Q.map
      (HomologicalComplex.extendMap (liftedTruncation p s h_p F)
        ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat _ 0 0 rfl).hom))

set_option backward.privateInPublic true in
private def liftedLocalComparison
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    [HasSheafify (Opens.grothendieckTopology T.obj.1.thickening) AddCommGrpCat.{u + 1}] :
    liftComplex.{u, u, u} _ (localAbelianComplex F T) ⟶
      ((siteAbelianInverseImageExact
        (Opens.grothendieckTopology T.obj.1.thickening)
        (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
        (smallOpensFunctor T)).obj.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (liftComplex _ (crystalDeRhamComplex p s h_p F)) :=
  ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (crystallineDeRhamLocalComparison p s h_p F T)

set_option backward.privateInPublic true in
private def localComparisonDerived
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    [HasSheafify (Opens.grothendieckTopology T.obj.1.thickening) AddCommGrpCat.{u + 1}] :
    crystalDeRhamOnTDerived F T ⟶
      (siteAbelianInverseImageDerived
        (Opens.grothendieckTopology T.obj.1.thickening)
        (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
        (smallOpensFunctor T)).obj (crystalDeRhamDerived p s h_p F) :=
  DerivedCategory.Q.map
    (HomologicalComplex.extendMap (liftedLocalComparison p s h_p F T)
      ComplexShape.embeddingUpNat ≫
      (ComplexShape.embeddingUpNat.mapAppIso
        (siteAbelianInverseImageExact
          (Opens.grothendieckTopology T.obj.1.thickening)
          (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
          (smallOpensFunctor T)).obj
        (liftComplex _ (crystalDeRhamComplex p s h_p F))).inv) ≫
    (siteAbelianInverseImageExact
      (Opens.grothendieckTopology T.obj.1.thickening)
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (smallOpensFunctor T)).obj.mapDerivedCategoryFactors.inv.app _

set_option backward.privateInPublic true in
/-- The derived global-sections image of the canonical comparison from the local
connection complex to the restricted crystalline de Rham complex. -/
def crystallineDeRhamLocalComparisonDerived
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    [HasSheafify (Opens.grothendieckTopology T.obj.1.thickening) AddCommGrpCat.{u + 1}] :
    (siteAbelianGlobalSectionsDerived.{u, u, u + 1, u + 1} (Opens.grothendieckTopology T.obj.1.thickening)).obj
      (crystalDeRhamOnTDerived F T) ⟶
    (siteAbelianGlobalSectionsDerived.{u, u, u + 1, u + 1} (Opens.grothendieckTopology T.obj.1.thickening)).obj
      ((siteAbelianInverseImageDerived
        (Opens.grothendieckTopology T.obj.1.thickening)
        (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
        (smallOpensFunctor T)).obj (crystalDeRhamDerived p s h_p F)) :=
  (siteAbelianGlobalSectionsDerived.{u, u, u + 1, u + 1} (Opens.grothendieckTopology T.obj.1.thickening)).map
    (localComparisonDerived p s h_p F T)

set_option backward.privateInPublic true in
/-- Restriction from crystalline derived global sections to the full local
divided-power de Rham complex.  Invertibility of the fixed truncation comparison
expresses the de Rham comparison theorem; invertibility of the fixed local
comparison expresses its identification on the thickening's Zariski site. -/
def crystallineRestrictionComplex [F.IsLocallyQuasiCoherent]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    [HasSheafify (Opens.grothendieckTopology T.obj.1.thickening) AddCommGrpCat.{u + 1}]
    (h_deRham : IsIso (crystallineDeRhamComparison p s h_p F))
    (h_local : IsIso (crystallineDeRhamLocalComparisonDerived p s h_p F T)) :
    (siteAbelianGlobalSectionsDerived _).obj (crystalCoefficientDerived p s h_p F) ⟶
      (siteAbelianGlobalSectionsDerived.{u, u, u + 1, u + 1} (Opens.grothendieckTopology T.obj.1.thickening)).obj
        (crystalDeRhamOnTDerived F T) :=
  @inv _ _ _ _ (crystallineDeRhamComparison p s h_p F) h_deRham ≫
    (Sheaf.derivedGlobalSectionsRestriction.{u, u, u + 1, u, u + 1, u + 1, u + 1} (smallOpensFunctor T)
      (Opens.grothendieckTopology T.obj.1.thickening)
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)).app
        (crystalDeRhamDerived p s h_p F) ≫
    @inv _ _ _ _ (crystallineDeRhamLocalComparisonDerived p s h_p F T) h_local

set_option backward.privateInPublic true in
/-- The crystalline restriction morphism is the inverse global de Rham
comparison followed by derived restriction and the inverse local comparison. -/
theorem crystallineRestrictionComplex_spec [F.IsLocallyQuasiCoherent]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    [HasSheafify (Opens.grothendieckTopology T.obj.1.thickening) AddCommGrpCat.{u + 1}]
    (h_deRham : IsIso (crystallineDeRhamComparison p s h_p F))
    (h_local : IsIso (crystallineDeRhamLocalComparisonDerived p s h_p F T)) :
    crystallineRestrictionComplex p s h_p F T h_deRham h_local =
      @inv _ _ _ _ (crystallineDeRhamComparison p s h_p F) h_deRham ≫
        (Sheaf.derivedGlobalSectionsRestriction.{u, u, u + 1, u, u + 1, u + 1, u + 1} (smallOpensFunctor T)
          (Opens.grothendieckTopology T.obj.1.thickening)
          (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)).app
            (crystalDeRhamDerived p s h_p F) ≫
        @inv _ _ _ _ (crystallineDeRhamLocalComparisonDerived p s h_p F T) h_local := rfl

end AlgebraicGeometry.Scheme.Crystalline
