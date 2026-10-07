module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import stacks_project.Chap63.Definition_63_12_1_LowerShriek
public import stacks_project.Chap63.Lemma_63_7_4_ClosedOpen

/-!
# Image of the complementary closed/open triangle under derived étale lower shriek

The functors `Rf_! ∘ j_!((-) |_U)` and `Rf_! ∘ i_* i⁻¹`, together with the
triangle obtained by applying `Rf_!` to `etaleDerivedClosedOpenTriangle`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Pretriangulated
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (X : Over Y) (P : Compactification.Of Y X)
variable {Z : Scheme.{u}} (i : Z ⟶ X.left) (Λ : Type u) [CommRing Λ]
variable [IsClosedImmersion i]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable [CompactSpace (closedImmersionComplement i).toScheme]
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [∀ F : (closedImmersionComplement i).toScheme.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (closedImmersionComplement i).ι).op.HasLeftKanExtension F]
variable [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback i).op.HasLeftKanExtension G]
variable [HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify
  (closedImmersionComplement i).toScheme.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [Abelian (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [Abelian
  (Sheaf (closedImmersionComplement i).toScheme.smallEtaleTopology
    (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory
  (Sheaf (closedImmersionComplement i).toScheme.smallEtaleTopology
    (ModuleCat.{u} Λ))]
variable [∀ U : Z.Etale,
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : (closedImmersionComplement i).toScheme.Etale,
  HasWeakSheafify
    ((closedImmersionComplement i).toScheme.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
variable [(etaleRestrictionSheaf (closedImmersionComplement i).ι
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleRestrictionSheaf (closedImmersionComplement i).ι (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleRestrictionSheaf (closedImmersionComplement i).ι (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero (closedImmersionComplement i).ι
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (closedImmersionComplement i).ι (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (closedImmersionComplement i).ι (ModuleCat.{u} Λ))]
variable [((smallEtalePullback i).sheafPullback (ModuleCat.{u} Λ)
    X.left.smallEtaleTopology Z.smallEtaleTopology).Additive]
variable [PreservesFiniteLimits
  ((smallEtalePullback i).sheafPullback (ModuleCat.{u} Λ)
    X.left.smallEtaleTopology Z.smallEtaleTopology)]
variable [PreservesFiniteColimits
  ((smallEtalePullback i).sheafPullback (ModuleCat.{u} Λ)
    X.left.smallEtaleTopology Z.smallEtaleTopology)]
variable [((smallEtalePullback i).sheafPushforwardContinuous (ModuleCat.{u} Λ)
    X.left.smallEtaleTopology Z.smallEtaleTopology).Additive]
variable [PreservesFiniteLimits
  ((smallEtalePullback i).sheafPushforwardContinuous (ModuleCat.{u} Λ)
    X.left.smallEtaleTopology Z.smallEtaleTopology)]
variable [PreservesFiniteColimits
  ((smallEtalePullback i).sheafPushforwardContinuous (ModuleCat.{u} Λ)
    X.left.smallEtaleTopology Z.smallEtaleTopology)]
variable [(moduleClosedOpenLower i Λ).Additive]
variable [(moduleClosedOpenClosed i Λ).Additive]
variable [PreservesFiniteLimits (moduleClosedOpenLower i Λ)]
variable [PreservesFiniteColimits (moduleClosedOpenLower i Λ)]
variable [PreservesFiniteLimits (moduleClosedOpenClosed i Λ)]
variable [PreservesFiniteColimits (moduleClosedOpenClosed i Λ)]
variable [(etaleDerivedLowerShriek X P : EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ).CommShift ℤ]

/-- The composite `Rf_! ∘ j_!((-) |_U)` on `D(X_étale, Λ)`, where
`j = (closedImmersionComplement i).ι`. On the source domain of Lemma 63.9.2
and Lemma 63.10.3 this is the compactification model of `Rg_!((-) |_U)`. -/
abbrev etaleDerivedLowerShriekRestrictOpen :
    EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ :=
  etaleDerivedExtensionByZeroRestrict (closedImmersionComplement i).ι Λ ⋙
    (etaleDerivedLowerShriek X P : EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ)

/-- `etaleDerivedLowerShriekRestrictOpen` evaluates as `Rf_!` of extension by
zero of the restriction to the open complement. -/
theorem etaleDerivedLowerShriekRestrictOpen_obj (K : EtaleDerived X.left Λ) :
    (etaleDerivedLowerShriekRestrictOpen X P i Λ).obj K =
      (etaleDerivedLowerShriek X P : EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ).obj
        ((etaleDerivedExtensionByZeroRestrict
            (closedImmersionComplement i).ι Λ).obj K) :=
  sorry

/-- The composite `Rf_! ∘ i_* i⁻¹` on `D(X_étale, Λ)`. On the source domain of
Lemma 63.9.2 and Lemma 63.10.3 this is the compactification model of
`Rh_!((-) |_Z)`. -/
abbrev etaleDerivedLowerShriekRestrictClosed :
    EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ :=
  etaleDerivedClosedOpenClosed i Λ ⋙
    (etaleDerivedLowerShriek X P : EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ)

/-- `etaleDerivedLowerShriekRestrictClosed` evaluates as `Rf_!` of derived
pushforward after pullback along the closed immersion. -/
theorem etaleDerivedLowerShriekRestrictClosed_obj (K : EtaleDerived X.left Λ) :
    (etaleDerivedLowerShriekRestrictClosed X P i Λ).obj K =
      (etaleDerivedLowerShriek X P : EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ).obj
        ((etaleDerivedClosedOpenClosed i Λ).obj K) :=
  sorry

/-- The image under `Rf_!` of the complementary closed/open triangle
`j_!(K|_U) ⟶ K ⟶ i_* i⁻¹ K ⟶ j_!(K|_U)⟦1⟧`. -/
def etaleDerivedLowerShriekClosedOpenTriangle (K : EtaleDerived X.left Λ) :
    Triangle (EtaleDerived Y Λ) :=
  (etaleDerivedLowerShriek X P : EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ).mapTriangle.obj
    (etaleDerivedClosedOpenTriangle i Λ K)

/-- The first vertex of the relative complementary triangle is
`Rf_!(j_!(K|_U))`. -/
theorem etaleDerivedLowerShriekClosedOpenTriangle_obj₁
    (K : EtaleDerived X.left Λ) :
    (etaleDerivedLowerShriekClosedOpenTriangle X P i Λ K).obj₁ =
      (etaleDerivedLowerShriekRestrictOpen X P i Λ).obj K :=
  sorry

/-- The middle vertex of the relative complementary triangle is `Rf_! K`. -/
theorem etaleDerivedLowerShriekClosedOpenTriangle_obj₂
    (K : EtaleDerived X.left Λ) :
    (etaleDerivedLowerShriekClosedOpenTriangle X P i Λ K).obj₂ =
      (etaleDerivedLowerShriek X P : EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ).obj K :=
  sorry

/-- The third vertex of the relative complementary triangle is
`Rf_!(i_* i⁻¹ K)`. -/
theorem etaleDerivedLowerShriekClosedOpenTriangle_obj₃
    (K : EtaleDerived X.left Λ) :
    (etaleDerivedLowerShriekClosedOpenTriangle X P i Λ K).obj₃ =
      (etaleDerivedLowerShriekRestrictClosed X P i Λ).obj K :=
  sorry

/-- The first morphism of the relative complementary triangle is `Rf_!` of the
derived extension-by-zero counit. -/
theorem etaleDerivedLowerShriekClosedOpenTriangle_mor₁
    (K : EtaleDerived X.left Λ) :
    (etaleDerivedLowerShriekClosedOpenTriangle X P i Λ K).mor₁ =
      (etaleDerivedLowerShriek X P : EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ).map
        ((etaleDerivedClosedOpenCounit i Λ).app K) :=
  sorry

/-- The second morphism of the relative complementary triangle is `Rf_!` of the
derived closed-immersion unit. -/
theorem etaleDerivedLowerShriekClosedOpenTriangle_mor₂
    (K : EtaleDerived X.left Λ) :
    (etaleDerivedLowerShriekClosedOpenTriangle X P i Λ K).mor₂ =
      (etaleDerivedLowerShriek X P : EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ).map
        ((etaleDerivedClosedOpenUnit i Λ).app K) :=
  sorry

/-- The third morphism of the relative complementary triangle is `Rf_!` of the
closed/open connecting map, composed with the shift comparison of `Rf_!`. -/
theorem etaleDerivedLowerShriekClosedOpenTriangle_mor₃
    (K : EtaleDerived X.left Λ) :
    (etaleDerivedLowerShriekClosedOpenTriangle X P i Λ K).mor₃ =
      (etaleDerivedLowerShriek X P : EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ).map (etaleDerivedClosedOpenδ i Λ K) ≫
        ((etaleDerivedLowerShriek X P : EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ).commShiftIso (1 : ℤ)).hom.app
          ((etaleDerivedClosedOpenTriangle i Λ K).obj₁) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
