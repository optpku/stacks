/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_91_13_Comparison
public import stacks_project.Chap63.Definition_63_12_1_Gamma
public import stacks_project.Chap63.Lemma_63_3_11_Comparison
public import stacks_project.Chap63.Lemma_63_9_4_Cartesian

/-!
# Stalks of derived étale lower shriek as compactly supported fibre cohomology

Canonical comparison `(Rf_! K)_ȳ ⟶ RΓ_c(X_ȳ, K|_{X_ȳ})` in `D(Λ)`, obtained
by applying `RΓ(Spec k, -)` to the cartesian identification of Lemma 63.9.4
along the geometric-fibre square of `f` at `ȳ`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Compactification
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Hom
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
open etaleDerivedLowerShriek

section FibreSetup

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (ybar : GeometricPoint Y)
variable (P : Of Y (Over.mk f))

/-- The structure morphism of the geometric fibre is of finite type, as a base
change of `f`. -/
instance finiteType_geometricFiberOverField_hom [Scheme.Hom.FiniteType f] :
    Scheme.Hom.FiniteType (geometricFiberOverField f ybar).hom :=
  sorry

/-- Compactification of the geometric fibre `X_ȳ ⟶ Spec k` obtained by
base-changing a compactification of `f` along `ȳ`. -/
abbrev geometricFiberCompactification :
    Of (Spec (CommRingCat.of ybar.K)) (geometricFiberOverField f ybar) :=
  compactificationPullback f ybar.hom (geometricFiberToPoint f ybar)
    (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P

/-- The fibre compactification is the cartesian pullback of `P` along `ȳ`. -/
theorem geometricFiberCompactification_eq :
    geometricFiberCompactification f ybar P =
      compactificationPullback f ybar.hom (geometricFiberToPoint f ybar)
        (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P :=
  sorry

/-- The interior immersion of the fibre compactification is the induced lift
`j'`. -/
theorem geometricFiberCompactification_ι :
    Of.ι (geometricFiberCompactification f ybar P) =
      interiorLift f ybar.hom (geometricFiberToPoint f ybar)
        (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P :=
  sorry

/-- The structure map of the fibre compactification is the ambient projection
`f̄'`. -/
theorem geometricFiberCompactification_hom :
    (geometricFiberCompactification f ybar P).obj.right.hom =
      ambientToBase f ybar.hom (geometricFiberToPoint f ybar)
        (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P :=
  sorry

/-- The spectrum of the residue field of a geometric point is quasi-compact. -/
instance compactSpace_specOfGeometricPoint :
    CompactSpace (Spec (CommRingCat.of ybar.K)) :=
  sorry

/-- The spectrum of the residue field of a geometric point is quasi-separated. -/
instance quasiSeparatedSpace_specOfGeometricPoint :
    QuasiSeparatedSpace (Spec (CommRingCat.of ybar.K)) :=
  sorry

/-- The geometric fibre of a finite-type morphism is quasi-compact. -/
instance compactSpace_geometricFiber [Scheme.Hom.FiniteType f] :
    CompactSpace (Hom.geometricFiber f ybar) :=
  sorry

/-- The geometric fibre of a finite-type morphism is quasi-separated. -/
instance quasiSeparatedSpace_geometricFiber [Scheme.Hom.FiniteType f]
    [IsSeparated f] :
    QuasiSeparatedSpace (Hom.geometricFiber f ybar) :=
  sorry

section GammaStalk

variable {Λ : Type u} [CommRing Λ]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify (Spec (CommRingCat.of ybar.K)).smallEtaleTopology
  (ModuleCat.{u} Λ)]
variable [HasWeakSheafify (Spec (CommRingCat.of ybar.K)).smallEtaleTopology
  (ModuleCat.{u} Λ)]
variable [∀ U : (Spec (CommRingCat.of ybar.K)).Etale,
  HasWeakSheafify ((Spec (CommRingCat.of ybar.K)).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (Spec (CommRingCat.of ybar.K)).smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback ybar.hom).op.HasLeftKanExtension F]
variable [HasDerivedCategory (ModuleCat.{u} Λ)]
variable [((sheafSections (Spec (CommRingCat.of ybar.K)).smallEtaleTopology
    (ModuleCat.{u} Λ)).obj
    (op (globalEtale (Spec (CommRingCat.of ybar.K))))).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((sheafSections (Spec (CommRingCat.of ybar.K)).smallEtaleTopology
        (ModuleCat.{u} Λ)).obj
      (op (globalEtale (Spec (CommRingCat.of ybar.K))))))
  (HomologicalComplex.quasiIso
    (Sheaf (Spec (CommRingCat.of ybar.K)).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]

/-- Geometric stalk `(K)_ȳ` in `D(Λ)`, read as `RΓ(Spec k, ȳ⁻¹ K)`. -/
def etaleDerivedGammaStalk (K : EtaleDerived Y Λ) :
    DerivedCategory (ModuleCat.{u} Λ) :=
  (etaleDerivedGamma (Spec (CommRingCat.of ybar.K)) Λ).obj
    ((etaleModuleDerivedInverseImage ybar.hom Λ).obj K)

/-- The geometric stalk is derived global sections of the inverse image along
`ȳ`. -/
theorem etaleDerivedGammaStalk_eq (K : EtaleDerived Y Λ) :
    etaleDerivedGammaStalk ybar K =
      (etaleDerivedGamma (Spec (CommRingCat.of ybar.K)) Λ).obj
        ((etaleModuleDerivedInverseImage ybar.hom Λ).obj K) :=
  sorry

end GammaStalk

end FibreSetup

-- Local instance justification (search instability): prefer the existing strong-to-weak projection for base topologies instead of repeatedly matching the section's over-site families.
attribute [local instance 10000] HasSheafify.isRightAdjoint

section CartesianGamma

variable {X Y X' Y' : Scheme.{u}}
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  (h_cart : IsPullback g' f' f g)
  [IsSeparated f] [Scheme.Hom.FiniteType f]
  [IsSeparated f'] [Scheme.Hom.FiniteType f']
  [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace X'] [QuasiSeparatedSpace X']
  [CompactSpace Y'] [QuasiSeparatedSpace Y']
  (P : Of Y (Over.mk f))
  (Λ : Type u) [CommRing Λ]

  [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : X'.Etale,
  HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Y'.Etale,
  HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify (ambient f g f' g' h_cart P).smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [HasWeakSheafify (ambient f g f' g' h_cart P).smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [∀ U : (ambient f g f' g' h_cart P).Etale,
  HasWeakSheafify ((ambient f g f' g' h_cart P).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf (ambient f g f' g' h_cart P).smallEtaleTopology (ModuleCat.{u} Λ))]

  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify (ambient f g f' g' h_cart P).smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify (ambient f g f' g' h_cart P).smallEtaleTopology
  AddCommGrpCat.{u}]

  [HasSheafCompose X.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose Y.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose X'.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose Y'.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose P.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose (ambient f g f' g' h_cart P).smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [X'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Y'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [P.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(ambient f g f' g' h_cart P).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g').op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback P.obj.right.hom).op.HasLeftKanExtension F]
  [∀ F : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ambientToBase f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ambientToSource f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ambientToBase f g f' g' h_cart P ≫ g)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToSource f g f' g' h_cart P ≫ P.obj.right.hom)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : (ambient f g f' g' h_cart P).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (interiorLift f g f' g' h_cart P ≫
      ambientToSource f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g' ≫ Of.ι P)).op.HasLeftKanExtension F]

  [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g').op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (ambientToSource f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g' : X' ⟶ (Over.mk f).left)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (g' : X' ⟶ (Over.mk f).left)).op.HasLeftKanExtension F]

  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback g).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback g').op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (ambientToSource f g f' g' h_cart P)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι P)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (interiorLift f g f' g' h_cart P)).op]

  [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]

  [(etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (interiorLift f g f' g' h_cart P)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero (interiorLift f g f' g' h_cart P) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero (interiorLift f g f' g' h_cart P) (ModuleCat.{u} Λ))]

  [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [((smallEtalePullback (ambientToBase f g f' g' h_cart P)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y'.smallEtaleTopology
    (ambient f g f' g' h_cart P).smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (ambientToBase f g f' g' h_cart P)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y'.smallEtaleTopology
      (ambient f g f' g' h_cart P).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (ambient f g f' g' h_cart P).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]

  [(etaleModulePushforward P.obj.right.hom Λ ⋙
    etaleModuleSheafPullback g Λ).Additive]
  [(etaleModuleSheafPullback (ambientToSource f g f' g' h_cart P) Λ ⋙
    etaleModulePushforward (ambientToBase f g f' g' h_cart P) Λ).Additive]
  [(etaleModulePushforward (ambientToBase f g f' g' h_cart P) Λ).Additive]
  [(etaleModulePushforward P.obj.right.hom Λ).Additive]


  [HasDerivedCategory (ModuleCat.{u} Λ)]
  [((sheafSections Y'.smallEtaleTopology (ModuleCat.{u} Λ)).obj
    (op (globalEtale Y'))).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((sheafSections Y'.smallEtaleTopology (ModuleCat.{u} Λ)).obj
      (op (globalEtale Y'))))
  (HomologicalComplex.quasiIso
    (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]

/-- `RΓ(Y', -)` applied to the unfolded cartesian comparison of Lemma 63.9.4. -/
def etaleDerivedLowerShriekGammaBaseChange_app (K : EtaleDerived X Λ) :=
  (etaleDerivedGamma Y' Λ).map
    ((baseChangeUnfolded f g f' g' h_cart P Λ).app K)

/-- Component of `etaleDerivedLowerShriekGammaBaseChange_app` is `RΓ` of the
unfolded lower-shriek base change. -/
theorem etaleDerivedLowerShriekGammaBaseChange_app_eq (K : EtaleDerived X Λ) :
    etaleDerivedLowerShriekGammaBaseChange_app f g f' g' h_cart P Λ K =
      (etaleDerivedGamma Y' Λ).map
        ((baseChangeUnfolded f g f' g' h_cart P Λ).app K) :=
  sorry

/-- On objects of `D⁺_tors(X_étale, Λ)`, `RΓ` of the cartesian comparison is an
isomorphism. -/
theorem isIso_etaleDerivedLowerShriekGammaBaseChange_app_of_isGE_isTorsion
    (K : EtaleDerived X Λ) (h_tors : etaleDerivedIsTorsion K)
    (n : ℤ) [DerivedCategory.IsGE K n] :
    IsIso (etaleDerivedLowerShriekGammaBaseChange_app f g f' g' h_cart P Λ K) :=
  sorry

/-- If `Λ` is torsion, `RΓ` of the cartesian comparison is an isomorphism. -/
theorem isIso_etaleDerivedLowerShriekGammaBaseChange_app_of_isTorsion
    (hΛ : AddMonoid.IsTorsion Λ) (K : EtaleDerived X Λ) :
    IsIso (etaleDerivedLowerShriekGammaBaseChange_app f g f' g' h_cart P Λ K) :=
  sorry

end CartesianGamma

section StalkComparison

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (ybar : GeometricPoint Y)
variable [IsSeparated f] [Scheme.Hom.FiniteType f]
variable [IsSeparated (geometricFiberOverField f ybar).hom]
variable [Scheme.Hom.FiniteType (geometricFiberOverField f ybar).hom]
variable [CompactSpace X] [QuasiSeparatedSpace X]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace (Hom.geometricFiber f ybar)]
variable [QuasiSeparatedSpace (Hom.geometricFiber f ybar)]
variable [CompactSpace (Spec (CommRingCat.of ybar.K))]
variable [QuasiSeparatedSpace (Spec (CommRingCat.of ybar.K))]
variable (P : Of Y (Over.mk f))
variable (Λ : Type u) [CommRing Λ]

variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify (Hom.geometricFiber f ybar).smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify (Hom.geometricFiber f ybar).smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : (Hom.geometricFiber f ybar).Etale,
  HasWeakSheafify ((Hom.geometricFiber f ybar).smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf (Hom.geometricFiber f ybar).smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify (Spec (CommRingCat.of ybar.K)).smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify (Spec (CommRingCat.of ybar.K)).smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : (Spec (CommRingCat.of ybar.K)).Etale,
  HasWeakSheafify ((Spec (CommRingCat.of ybar.K)).smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf (Spec (CommRingCat.of ybar.K)).smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify (ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [HasWeakSheafify (ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [∀ U : (ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).Etale,
  HasWeakSheafify ((ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf (ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).smallEtaleTopology (ModuleCat.{u} Λ))]

  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify (Hom.geometricFiber f ybar).smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify (Spec (CommRingCat.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify (ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify (Hom.geometricFiber f ybar).smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify (Spec (CommRingCat.of ybar.K)).smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify (ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).smallEtaleTopology
  AddCommGrpCat.{u}]

  [HasSheafCompose X.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose Y.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose (Hom.geometricFiber f ybar).smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose (Spec (CommRingCat.of ybar.K)).smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose P.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose (ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(Hom.geometricFiber f ybar).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(Spec (CommRingCat.of ybar.K)).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [P.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback ybar.hom).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (geometricFiberToX f ybar)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback P.obj.right.hom).op.HasLeftKanExtension F]
  [∀ F : (Spec (CommRingCat.of ybar.K)).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ambientToBase f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ambientToSource f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ambientToBase f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P ≫ ybar.hom)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToSource f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P ≫ P.obj.right.hom)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : (ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (interiorLift f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (interiorLift f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P ≫
      ambientToSource f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (geometricFiberToX f ybar ≫ Of.ι P)).op.HasLeftKanExtension F]

  [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback ybar.hom).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (geometricFiberToX f ybar)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (ambientToSource f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (geometricFiberToX f ybar : Hom.geometricFiber f ybar ⟶ (Over.mk f).left)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (geometricFiberToX f ybar : Hom.geometricFiber f ybar ⟶ (Over.mk f).left)).op.HasLeftKanExtension F]

  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback ybar.hom).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (geometricFiberToX f ybar)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (ambientToSource f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι P)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (interiorLift f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)).op]

  [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : (Hom.geometricFiber f ybar).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (interiorLift f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)).op.HasLeftKanExtension F]
  [∀ F : (Hom.geometricFiber f ybar).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (interiorLift f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]

  [(etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (interiorLift f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero (interiorLift f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero (interiorLift f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P) (ModuleCat.{u} Λ))]

  [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [((smallEtalePullback (ambientToBase f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) (Spec (CommRingCat.of ybar.K)).smallEtaleTopology
    (ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (ambientToBase f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (Spec (CommRingCat.of ybar.K)).smallEtaleTopology
      (ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (ambient f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]

  [(etaleModulePushforward P.obj.right.hom Λ ⋙
    etaleModuleSheafPullback ybar.hom Λ).Additive]
  [(etaleModuleSheafPullback (ambientToSource f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P) Λ ⋙
    etaleModulePushforward (ambientToBase f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P) Λ).Additive]
  [(etaleModulePushforward (ambientToBase f ybar.hom (geometricFiberToPoint f ybar) (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P) Λ).Additive]
  [(etaleModulePushforward P.obj.right.hom Λ).Additive]


  [HasDerivedCategory (ModuleCat.{u} Λ)]
  [((sheafSections (Spec (CommRingCat.of ybar.K)).smallEtaleTopology (ModuleCat.{u} Λ)).obj
    (op (globalEtale (Spec (CommRingCat.of ybar.K))))).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((sheafSections (Spec (CommRingCat.of ybar.K)).smallEtaleTopology (ModuleCat.{u} Λ)).obj
      (op (globalEtale (Spec (CommRingCat.of ybar.K))))))
  (HomologicalComplex.quasiIso
    (Sheaf (Spec (CommRingCat.of ybar.K)).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]

/-- Objectwise comparison `(Rf_! K)_ȳ ⟶ RΓ_c(X_ȳ, K|_{X_ȳ})`, obtained by
applying `RΓ(Spec k, -)` to Lemma 63.9.4 on the geometric-fibre square of
`f` at `ȳ`. -/
def etaleDerivedLowerShriekStalkCompactSupport_app (K : EtaleDerived X Λ) :
    etaleDerivedGammaStalk ybar
        ((etaleDerivedLowerShriek (Over.mk f) P).obj K) ⟶
      (etaleDerivedGammaCompactSupport
          (geometricFiberCompactification f ybar P)).obj
        ((etaleModuleDerivedInverseImage (geometricFiberToX f ybar) Λ).obj K) :=
  (etaleDerivedGamma (Spec (CommRingCat.of ybar.K)) Λ).map
    ((baseChangeUnfolded f ybar.hom (geometricFiberToPoint f ybar)
        (geometricFiberToX f ybar) (geometricFiber_isPullback f ybar) P Λ).app K)

/-- Canonical comparison of functors `D(X_étale, Λ) ⥤ D(Λ)` obtained by
applying `RΓ(Spec k, -)` to Lemma 63.9.4 on the geometric fibre of `f` at
`ȳ`. -/
def etaleDerivedLowerShriekStalkCompactSupport :
    (etaleDerivedLowerShriek (Over.mk f) P ⋙
        etaleModuleDerivedInverseImage ybar.hom Λ ⋙
        etaleDerivedGamma (Spec (CommRingCat.of ybar.K)) Λ) ⟶
      (etaleModuleDerivedInverseImage (geometricFiberToX f ybar) Λ ⋙
        etaleDerivedGammaCompactSupport
          (geometricFiberCompactification f ybar P)) where
  app K := etaleDerivedLowerShriekStalkCompactSupport_app f ybar P Λ K
  naturality := sorry

/-- The objectwise comparison is the component of
`etaleDerivedLowerShriekStalkCompactSupport`. -/
theorem etaleDerivedLowerShriekStalkCompactSupport_app_eq
    (K : EtaleDerived X Λ) :
    etaleDerivedLowerShriekStalkCompactSupport_app f ybar P Λ K =
      (etaleDerivedLowerShriekStalkCompactSupport f ybar P Λ).app K :=
  sorry

/-- On objects of `D⁺_tors(X_étale, Λ)`, the stalk comparison is an
isomorphism. -/
theorem isIso_etaleDerivedLowerShriekStalkCompactSupport_of_isGE_isTorsion
    (K : EtaleDerived X Λ) (h_tors : etaleDerivedIsTorsion K)
    (n : ℤ) [DerivedCategory.IsGE K n] :
    IsIso (etaleDerivedLowerShriekStalkCompactSupport_app f ybar P Λ K) :=
  sorry

/-- If `Λ` is torsion, the stalk comparison is an isomorphism on all of
`D(X_étale, Λ)`. -/
theorem isIso_etaleDerivedLowerShriekStalkCompactSupport_of_isTorsion
    (hΛ : AddMonoid.IsTorsion Λ) (K : EtaleDerived X Λ) :
    IsIso (etaleDerivedLowerShriekStalkCompactSupport_app f ybar P Λ K) :=
  sorry

/-- If `Λ` is torsion, the functorial stalk comparison is an isomorphism. -/
theorem isIso_etaleDerivedLowerShriekStalkCompactSupport_natTrans_of_isTorsion
    (hΛ : AddMonoid.IsTorsion Λ) :
    IsIso (etaleDerivedLowerShriekStalkCompactSupport f ybar P Λ) :=
  sorry

end StalkComparison




end AlgebraicGeometry.Scheme.Etale

end
