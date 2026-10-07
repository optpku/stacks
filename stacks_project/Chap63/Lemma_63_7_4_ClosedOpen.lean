module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.Algebra.Homology.DerivedCategory.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Complement
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import stacks_project.Chap63.Lemma_63_7_3_ExtensionByZero

/-!
# Complementary closed/open triangle in `D(X_étale, Λ)`

Sheaf-level complementary SES and the derived triangle
`j_! j⁻¹ K ⟶ K ⟶ i_* i⁻¹ K ⟶ j_! j⁻¹ K⟦1⟧` attached to a closed immersion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Pretriangulated CategoryTheory.Localization
open AlgebraicGeometry ComplexShape

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Etale

/-- Pin `HasZeroMorphisms` on étale `Λ`-module sheaves to the preadditive instance
used by `DerivedCategory.Q` and cochain complexes. -/
instance (priority := 10000) etaleModuleSheaf_hasZeroMorphisms
    (Y : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    [Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))] :
    HasZeroMorphisms (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) :=
  Preadditive.preadditiveHasZeroMorphisms

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
variable (Λ : Type v) [CommRing Λ]
variable [∀ F : (closedImmersionComplement i).toScheme.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
    (etaleRestriction (closedImmersionComplement i).ι).op.HasLeftKanExtension F]
variable [∀ G : X.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
    (smallEtalePullback i).op.HasLeftKanExtension G]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [HasWeakSheafify (closedImmersionComplement i).toScheme.smallEtaleTopology
    (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [Abelian (Sheaf Z.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [Abelian (Sheaf (closedImmersionComplement i).toScheme.smallEtaleTopology
    (ModuleCat.{v} Λ))]

/-- The exact endofunctor `j_! ∘ j⁻¹` on sheaves of `Λ`-modules on `X_étale`,
where `j = (closedImmersionComplement i).ι`. -/
def moduleClosedOpenLower :
    Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ) :=
  etaleRestrictionSheaf (closedImmersionComplement i).ι (ModuleCat.{v} Λ) ⋙
    etaleExtensionByZero (closedImmersionComplement i).ι (ModuleCat.{v} Λ)

/-- `moduleClosedOpenLower` is extension by zero after étale restriction along
the open complement inclusion. -/
theorem moduleClosedOpenLower_obj
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) :
    (moduleClosedOpenLower i Λ).obj F =
      (etaleExtensionByZero (closedImmersionComplement i).ι (ModuleCat.{v} Λ)).obj
        ((etaleRestrictionSheaf (closedImmersionComplement i).ι
          (ModuleCat.{v} Λ)).obj F) := sorry

/-- The exact endofunctor `i_* ∘ i⁻¹` on sheaves of `Λ`-modules on `X_étale`. -/
def moduleClosedOpenClosed :
    Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ) :=
  (smallEtalePullback i).sheafPullback (ModuleCat.{v} Λ)
      X.smallEtaleTopology Z.smallEtaleTopology ⋙
    (smallEtalePullback i).sheafPushforwardContinuous (ModuleCat.{v} Λ)
      X.smallEtaleTopology Z.smallEtaleTopology

/-- `moduleClosedOpenClosed` is small-étale pushforward after pullback along
the closed immersion. -/
theorem moduleClosedOpenClosed_obj
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) :
    (moduleClosedOpenClosed i Λ).obj F =
      ((smallEtalePullback i).sheafPushforwardContinuous (ModuleCat.{v} Λ)
          X.smallEtaleTopology Z.smallEtaleTopology).obj
        (((smallEtalePullback i).sheafPullback (ModuleCat.{v} Λ)
            X.smallEtaleTopology Z.smallEtaleTopology).obj F) := sorry

/-- The adjunction counit natural transformation `j_! ∘ j⁻¹ ⟶ 𝟭`. -/
def moduleClosedOpenCounitNat :
    moduleClosedOpenLower i Λ ⟶
      𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) :=
  (etaleExtensionByZero_adjunction (closedImmersionComplement i).ι
    (ModuleCat.{v} Λ)).counit

/-- The adjunction unit natural transformation `𝟭 ⟶ i_* ∘ i⁻¹`. -/
def moduleClosedOpenUnitNat :
    𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ⟶
      moduleClosedOpenClosed i Λ :=
  ((smallEtalePullback i).sheafAdjunctionContinuous (ModuleCat.{v} Λ)
      X.smallEtaleTopology Z.smallEtaleTopology).unit

/-- The adjunction counit `j_! (j⁻¹ F) ⟶ F` for the open complement inclusion
`j = (closedImmersionComplement i).ι`. -/
def moduleClosedOpenCounit (F : Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) :
    (moduleClosedOpenLower i Λ).obj F ⟶ F :=
  (moduleClosedOpenCounitNat i Λ).app F

/-- The adjunction unit `F ⟶ i_* (i⁻¹ F)` of small-étale inverse image and
direct image along a closed immersion. -/
def moduleClosedOpenUnit (F : Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) :
    F ⟶ (moduleClosedOpenClosed i Λ).obj F :=
  (moduleClosedOpenUnitNat i Λ).app F

/-- The two complementary maps compose to zero. -/
theorem moduleClosedOpen_comp_zero
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) :
    moduleClosedOpenCounit i Λ F ≫ moduleClosedOpenUnit i Λ F = 0 := sorry

/-- The underived complementary closed/open short complex
`j_! j⁻¹ F ⟶ F ⟶ i_* i⁻¹ F` of sheaves of `Λ`-modules on `X_étale`. -/
def moduleClosedOpenShortComplex
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) :
    ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) where
  f := moduleClosedOpenCounit i Λ F
  g := moduleClosedOpenUnit i Λ F
  zero := moduleClosedOpen_comp_zero i Λ F

/-- The first map of `moduleClosedOpenShortComplex` is the extension-by-zero
counit. -/
theorem moduleClosedOpenShortComplex_f
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) :
    (moduleClosedOpenShortComplex i Λ F).f = moduleClosedOpenCounit i Λ F := sorry

/-- The second map of `moduleClosedOpenShortComplex` is the closed-immersion
direct-image unit. -/
theorem moduleClosedOpenShortComplex_g
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) :
    (moduleClosedOpenShortComplex i Λ F).g = moduleClosedOpenUnit i Λ F := sorry

/-- The complementary sequence of sheaves of `Λ`-modules is short exact. -/
theorem moduleClosedOpenShortComplex_shortExact
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) :
    (moduleClosedOpenShortComplex i Λ F).ShortExact := sorry

variable [(etaleRestrictionSheaf (closedImmersionComplement i).ι (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
    (etaleRestrictionSheaf (closedImmersionComplement i).ι (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
    (etaleRestrictionSheaf (closedImmersionComplement i).ι (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero (closedImmersionComplement i).ι (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
    (etaleExtensionByZero (closedImmersionComplement i).ι (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
    (etaleExtensionByZero (closedImmersionComplement i).ι (ModuleCat.{v} Λ))]
variable [((smallEtalePullback i).sheafPullback (ModuleCat.{v} Λ)
    X.smallEtaleTopology Z.smallEtaleTopology).Additive]
variable [PreservesFiniteLimits
    ((smallEtalePullback i).sheafPullback (ModuleCat.{v} Λ)
      X.smallEtaleTopology Z.smallEtaleTopology)]
variable [PreservesFiniteColimits
    ((smallEtalePullback i).sheafPullback (ModuleCat.{v} Λ)
      X.smallEtaleTopology Z.smallEtaleTopology)]
variable [((smallEtalePullback i).sheafPushforwardContinuous (ModuleCat.{v} Λ)
    X.smallEtaleTopology Z.smallEtaleTopology).Additive]
variable [PreservesFiniteLimits
    ((smallEtalePullback i).sheafPushforwardContinuous (ModuleCat.{v} Λ)
      X.smallEtaleTopology Z.smallEtaleTopology)]
variable [PreservesFiniteColimits
    ((smallEtalePullback i).sheafPushforwardContinuous (ModuleCat.{v} Λ)
      X.smallEtaleTopology Z.smallEtaleTopology)]
variable [(moduleClosedOpenLower i Λ).Additive]
variable [(moduleClosedOpenClosed i Λ).Additive]
variable [PreservesFiniteLimits (moduleClosedOpenLower i Λ)]
variable [PreservesFiniteColimits (moduleClosedOpenLower i Λ)]
variable [PreservesFiniteLimits (moduleClosedOpenClosed i Λ)]
variable [PreservesFiniteColimits (moduleClosedOpenClosed i Λ)]

/-- Degreewise cochain map associated to the extension-by-zero counit. -/
def moduleClosedOpenCochainCounit
    (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ) :
    ((etaleRestrictionSheaf (closedImmersionComplement i).ι
            (ModuleCat.{v} Λ)).mapHomologicalComplex (up ℤ) ⋙
        (etaleExtensionByZero (closedImmersionComplement i).ι
          (ModuleCat.{v} Λ)).mapHomologicalComplex (up ℤ)).obj K ⟶ K where
  f n := moduleClosedOpenCounit i Λ (K.X n)
  comm' := sorry

/-- Degreewise cochain map associated to the closed-immersion unit. -/
def moduleClosedOpenCochainUnit
    (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ) :
    K ⟶ (((smallEtalePullback i).sheafPullback (ModuleCat.{v} Λ)
            X.smallEtaleTopology Z.smallEtaleTopology).mapHomologicalComplex (up ℤ) ⋙
        ((smallEtalePullback i).sheafPushforwardContinuous (ModuleCat.{v} Λ)
          X.smallEtaleTopology Z.smallEtaleTopology).mapHomologicalComplex (up ℤ)).obj K where
  f n := moduleClosedOpenUnit i Λ (K.X n)
  comm' := sorry

/-- The complementary maps remain zero after applying the functors degreewise
to a cochain complex. -/
theorem moduleClosedOpenCochain_comp_zero
    (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ) :
    moduleClosedOpenCochainCounit i Λ K ≫ moduleClosedOpenCochainUnit i Λ K = 0 := sorry

/-- The cochain-complex lift of the complementary closed/open short complex. -/
def moduleClosedOpenCochainShortComplex
    (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ) :
    ShortComplex
      (CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ) where
  X₁ := ((etaleRestrictionSheaf (closedImmersionComplement i).ι
            (ModuleCat.{v} Λ)).mapHomologicalComplex (up ℤ) ⋙
        (etaleExtensionByZero (closedImmersionComplement i).ι
          (ModuleCat.{v} Λ)).mapHomologicalComplex (up ℤ)).obj K
  X₂ := K
  X₃ := (((smallEtalePullback i).sheafPullback (ModuleCat.{v} Λ)
            X.smallEtaleTopology Z.smallEtaleTopology).mapHomologicalComplex (up ℤ) ⋙
        ((smallEtalePullback i).sheafPushforwardContinuous (ModuleCat.{v} Λ)
          X.smallEtaleTopology Z.smallEtaleTopology).mapHomologicalComplex (up ℤ)).obj K
  f := moduleClosedOpenCochainCounit i Λ K
  g := moduleClosedOpenCochainUnit i Λ K
  zero := moduleClosedOpenCochain_comp_zero i Λ K

/-- The cochain-level complementary sequence is short exact. -/
theorem moduleClosedOpenCochainShortComplex_shortExact
    (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ) :
    (moduleClosedOpenCochainShortComplex i Λ K).ShortExact := sorry

variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory
    (Sheaf (closedImmersionComplement i).toScheme.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ U : X.Etale,
    HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
variable [∀ U : Z.Etale,
    HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
variable [∀ U : (closedImmersionComplement i).toScheme.Etale,
    HasWeakSheafify
      ((closedImmersionComplement i).toScheme.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]

/-- The derived adjunction counit `j_! j⁻¹ ⟶ 𝟭` on `EtaleDerived X Λ`. -/
def etaleDerivedClosedOpenCounit :
    etaleDerivedExtensionByZeroRestrict (closedImmersionComplement i).ι Λ ⟶
      𝟭 (EtaleDerived X Λ) :=
  (etaleDerivedExtensionByZeroAdjunction (closedImmersionComplement i).ι Λ).counit

/-- The derived functor `i_* i⁻¹` on `EtaleDerived X Λ`. -/
def etaleDerivedClosedOpenClosed :
    EtaleDerived X Λ ⥤ EtaleDerived X Λ :=
  ((smallEtalePullback i).sheafPullback (ModuleCat.{v} Λ)
      X.smallEtaleTopology Z.smallEtaleTopology).mapDerivedCategory ⋙
    ((smallEtalePullback i).sheafPushforwardContinuous (ModuleCat.{v} Λ)
      X.smallEtaleTopology Z.smallEtaleTopology).mapDerivedCategory

/-- `etaleDerivedClosedOpenClosed` evaluates as derived pushforward after derived
pullback along the closed immersion. -/
theorem etaleDerivedClosedOpenClosed_obj (K : EtaleDerived X Λ) :
    (etaleDerivedClosedOpenClosed i Λ).obj K =
      ((smallEtalePullback i).sheafPushforwardContinuous (ModuleCat.{v} Λ)
          X.smallEtaleTopology Z.smallEtaleTopology).mapDerivedCategory.obj
        (((smallEtalePullback i).sheafPullback (ModuleCat.{v} Λ)
            X.smallEtaleTopology Z.smallEtaleTopology).mapDerivedCategory.obj K) :=
  sorry

/-- The derived adjunction unit `𝟭 ⟶ i_* i⁻¹` on `EtaleDerived X Λ`. -/
def etaleDerivedClosedOpenUnit :
    𝟭 (EtaleDerived X Λ) ⟶ etaleDerivedClosedOpenClosed i Λ :=
  (Adjunction.mapDerivedCategory
    ((smallEtalePullback i).sheafAdjunctionContinuous (ModuleCat.{v} Λ)
      X.smallEtaleTopology Z.smallEtaleTopology)).unit

/-- The connecting morphism of the complementary triangle, obtained from
`triangleOfSESδ` of a cochain representative and transported along
`mapDerivedCategoryFactors`. -/
def etaleDerivedClosedOpenδ (K : EtaleDerived X Λ) :
    (etaleDerivedClosedOpenClosed i Λ).obj K ⟶
      ((etaleDerivedExtensionByZeroRestrict (closedImmersionComplement i).ι Λ).obj K)⟦(1 : ℤ)⟧ :=
  let j := (closedImmersionComplement i).ι
  let K' := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  let res := etaleRestrictionSheaf j (ModuleCat.{v} Λ)
  let ext0 := etaleExtensionByZero j (ModuleCat.{v} Λ)
  let pull := (smallEtalePullback i).sheafPullback (ModuleCat.{v} Λ)
    X.smallEtaleTopology Z.smallEtaleTopology
  let push := (smallEtalePullback i).sheafPushforwardContinuous (ModuleCat.{v} Λ)
    X.smallEtaleTopology Z.smallEtaleTopology
  (etaleDerivedClosedOpenClosed i Λ).map e.inv ≫
    push.mapDerivedCategory.map (pull.mapDerivedCategoryFactors.hom.app K') ≫
      push.mapDerivedCategoryFactors.hom.app ((pull.mapHomologicalComplex (up ℤ)).obj K') ≫
        DerivedCategory.triangleOfSESδ
          (moduleClosedOpenCochainShortComplex_shortExact i Λ K') ≫
          (ext0.mapDerivedCategoryFactors.inv.app
              ((res.mapHomologicalComplex (up ℤ)).obj K'))⟦(1 : ℤ)⟧' ≫
            (ext0.mapDerivedCategory.map
                (res.mapDerivedCategoryFactors.inv.app K'))⟦(1 : ℤ)⟧' ≫
              ((etaleDerivedExtensionByZeroRestrict j Λ).map e.hom)⟦(1 : ℤ)⟧'

/-- The complementary closed/open triangle
`j_! j⁻¹ K ⟶ K ⟶ i_* i⁻¹ K ⟶ j_! j⁻¹ K⟦1⟧` in `EtaleDerived X Λ`. -/
def etaleDerivedClosedOpenTriangle (K : EtaleDerived X Λ) :
    Triangle (EtaleDerived X Λ) :=
  Triangle.mk ((etaleDerivedClosedOpenCounit i Λ).app K)
    ((etaleDerivedClosedOpenUnit i Λ).app K) (etaleDerivedClosedOpenδ i Λ K)

/-- The first vertex of the complementary triangle is `j_! j⁻¹ K`. -/
theorem etaleDerivedClosedOpenTriangle_obj₁ (K : EtaleDerived X Λ) :
    (etaleDerivedClosedOpenTriangle i Λ K).obj₁ =
      (etaleDerivedExtensionByZeroRestrict (closedImmersionComplement i).ι Λ).obj K :=
  sorry

/-- The middle vertex of the complementary triangle is `K`. -/
theorem etaleDerivedClosedOpenTriangle_obj₂ (K : EtaleDerived X Λ) :
    (etaleDerivedClosedOpenTriangle i Λ K).obj₂ = K := sorry

/-- The third vertex of the complementary triangle is `i_* i⁻¹ K`. -/
theorem etaleDerivedClosedOpenTriangle_obj₃ (K : EtaleDerived X Λ) :
    (etaleDerivedClosedOpenTriangle i Λ K).obj₃ =
      (etaleDerivedClosedOpenClosed i Λ).obj K := sorry

/-- The first morphism of the complementary triangle is the derived counit. -/
theorem etaleDerivedClosedOpenTriangle_mor₁ (K : EtaleDerived X Λ) :
    (etaleDerivedClosedOpenTriangle i Λ K).mor₁ =
      (etaleDerivedClosedOpenCounit i Λ).app K := sorry

/-- The second morphism of the complementary triangle is the derived unit. -/
theorem etaleDerivedClosedOpenTriangle_mor₂ (K : EtaleDerived X Λ) :
    (etaleDerivedClosedOpenTriangle i Λ K).mor₂ =
      (etaleDerivedClosedOpenUnit i Λ).app K := sorry

/-- The third morphism of the complementary triangle is the transported
connecting map of the cochain-level short exact sequence. -/
theorem etaleDerivedClosedOpenTriangle_mor₃ (K : EtaleDerived X Λ) :
    (etaleDerivedClosedOpenTriangle i Λ K).mor₃ =
      etaleDerivedClosedOpenδ i Λ K := sorry

end AlgebraicGeometry.Scheme.Etale
