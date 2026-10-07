module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Additive
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Naturality
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Cohomology.AffineBase
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.CupProduct
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.DerivedPushforward
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.Cohomology

-- Local instance justification (defeq pin): the total-derived direct-image unit must use the `ModuleDerived` presentation of `DerivedPushforward.derivedComplex`.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

variable {X Y S T : Scheme.{u}} {f : X ⟶ Y} {a : X ⟶ S} {b : Y ⟶ T} {g : S ⟶ T}

/-- The identity square comparing a morphism to an affine scheme with its canonical affine
presentation commutes. -/
theorem baseRingSquare_comm (p : X ⟶ S) [IsAffine S] :
    𝟙 X ≫ (p ≫ S.isoSpec.hom) = p ≫ S.isoSpec.hom := sorry

/-- The coefficient square comparing a morphism with the canonical affine presentation of its
base. -/
theorem baseRingSquare (p : X ⟶ S) [IsAffine S] :
    CommSq (𝟙 X) p (p ≫ S.isoSpec.hom) S.isoSpec.hom := sorry

/-- Restriction from coefficients over the canonical affine presentation back to the original
affine base. -/
noncomputable abbrev baseRingRestriction (p : X ⟶ S) [IsAffine S] :
    coefficientRing (p ≫ S.isoSpec.hom) →+* coefficientRing p :=
  (RingedSite.Hom.globalSectionsMap.{u, u, u, u, u}
    (RingedSpace.DeRham.baseChangeHom.{u}
      ((baseRingSquare p).map (Scheme.forgetToLocallyRingedSpace ⋙
        LocallyRingedSpace.forgetToSheafedSpace)))).hom

/-- The restriction map is induced by the coefficient-site comparison square. -/
theorem baseRingRestriction_def (p : X ⟶ S) [IsAffine S] :
    baseRingRestriction p =
      (RingedSite.Hom.globalSectionsMap.{u, u, u, u, u}
        (RingedSpace.DeRham.baseChangeHom.{u}
          ((baseRingSquare p).map (Scheme.forgetToLocallyRingedSpace ⋙
            LocallyRingedSpace.forgetToSheafedSpace)))).hom := sorry

/-- The canonical map from the global functions on an affine base to the global sections of the
inverse-image coefficient sheaf. -/
noncomputable abbrev baseRingMap (p : X ⟶ S) [IsAffine S] :
    Scheme.globalSectionsRing S →+* coefficientRing p :=
  (baseRingRestriction p).comp (baseRingMapOfAffineTarget (p ≫ S.isoSpec.hom)).hom

/-- The base-ring map factors through the coefficient ring for the canonical affine
presentation of the base. -/
theorem baseRingMap_def (p : X ⟶ S) [IsAffine S] :
    baseRingMap p =
      (baseRingRestriction p).comp
        (baseRingMapOfAffineTarget (p ≫ S.isoSpec.hom)).hom := sorry

/-- Relative de Rham cohomology regarded as a module over the global functions on the base. -/
noncomputable abbrev overBase (p : X ⟶ S) [IsAffine S] (q : ℤ) :
    ModuleCat.{u} (Scheme.globalSectionsRing S) :=
  (ModuleCat.restrictScalars (baseRingMap p)).obj (cohomology p q)

/-- `overBase` is restriction of the coefficient-ring action along `baseRingMap`. -/
theorem overBase_def (p : X ⟶ S) [IsAffine S] (q : ℤ) :
    overBase p q =
      (ModuleCat.restrictScalars (baseRingMap p)).obj (cohomology p q) := sorry

/-- Transport relative de Rham cohomology across an equality of cohomological degrees. -/
noncomputable def castDegree (p : X ⟶ S) [IsAffine S] {i j : ℤ} (h : i = j) :
    overBase p i ⟶ overBase p j :=
  eqToHom (congrArg (overBase p) h)

/-- Degree transport along reflexivity is the identity morphism. -/
theorem castDegree_rfl (p : X ⟶ S) [IsAffine S] (q : ℤ) :
    castDegree p (rfl : q = q) = 𝟙 (overBase p q) := sorry

/-- The morphism of coefficient ringed sites associated to a triangle over `S`. -/
noncomputable abbrev coefficientHom (sq : CommSq f a b g) :
    RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom ⟶
      RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom :=
  RingedSpace.DeRham.baseChangeHom
    (sq.map (Scheme.forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace))

/-- `coefficientHom` is the coefficient morphism induced by the underlying ringed-space
commutative square. -/
theorem coefficientHom_def (sq : CommSq f a b g) :
    coefficientHom sq =
      RingedSpace.DeRham.baseChangeHom
        (sq.map (Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace)) := sorry

/-- The relative de Rham complex map of a triangle, extended from `ℕ` to `ℤ`. -/
noncomputable def extendedPullback (sq : CommSq f a b g) :
    extendedDeRhamComplex b ⟶
      (modulePushforwardComplex (coefficientHom sq)).obj (extendedDeRhamComplex a) :=
  HomologicalComplex.extendMap
      (RingedSpace.DeRham.map
        (sq.map (Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace))) embeddingUpNat ≫
    (embeddingUpNat.mapAppIso
      (modulePushforward (coefficientHom sq))
      (RingedSpace.DeRham.complex a.toLRSHom.toShHom)).inv

/-- The extended pullback is induced by the relative de Rham map and the canonical comparison
between extension and direct image. -/
theorem extendedPullback_def (sq : CommSq f a b g) :
    extendedPullback sq =
      HomologicalComplex.extendMap
          (RingedSpace.DeRham.map
            (sq.map (Scheme.forgetToLocallyRingedSpace ⋙
              LocallyRingedSpace.forgetToSheafedSpace))) embeddingUpNat ≫
        (embeddingUpNat.mapAppIso
          (modulePushforward (coefficientHom sq))
          (RingedSpace.DeRham.complex a.toLRSHom.toShHom)).inv := sorry

/-- The derived relative de Rham pullback morphism attached to a commutative triangle. -/
noncomputable def derivedPullback (sq : CommSq f a b g)
    [hPull : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (coefficientHom sq))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))] :
    DerivedPushforward.derivedComplex b ⟶
      (modulePushforwardDerived.{u} (coefficientHom sq)).obj (DerivedPushforward.derivedComplex a) :=
  (moduleLocalization.{u}
      (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom)).map
      ((HomotopyCategory.quotient _ (up ℤ)).map (extendedPullback sq)) ≫
    (Functor.totalRightDerivedUnit
      (modulePushforwardToDerived.{u} (coefficientHom sq))
      (moduleLocalization.{u}
        (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))
      (ModuleQis.{u}
        (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))).app
      ((HomotopyCategory.quotient _ (up ℤ)).obj (extendedDeRhamComplex a))

/-- The derived pullback is localization of `extendedPullback` followed by the canonical
total-right-derived unit for direct image. -/
theorem derivedPullback_spec (sq : CommSq f a b g)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (coefficientHom sq))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))] :
    derivedPullback sq =
      (moduleLocalization.{u}
        (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom)).map
          ((HomotopyCategory.quotient _ (up ℤ)).map (extendedPullback sq)) ≫
        (Functor.totalRightDerivedUnit
          (modulePushforwardToDerived.{u} (coefficientHom sq))
          (moduleLocalization.{u}
            (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))
          (ModuleQis.{u}
            (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))).app
          ((HomotopyCategory.quotient _ (up ℤ)).obj (extendedDeRhamComplex a)) := sorry

/-- Relative de Rham cohomology of `a`, with scalars restricted along the coefficient map of
the triangle. -/
noncomputable abbrev restricted (sq : CommSq f a b g) (q : ℤ) :=
  (globalSectionsRestriction.{u} (coefficientHom sq)).obj (cohomology a q)

/-- Restricted cohomology is restriction of scalars along the coefficient global-sections map. -/
theorem restricted_def (sq : CommSq f a b g) (q : ℤ) :
    restricted sq q =
      (globalSectionsRestriction.{u} (coefficientHom sq)).obj (cohomology a q) := sorry

/-- The homotopy-level source for the specialized global-sections comparison. -/
noncomputable abbrev comparisonSource (sq : CommSq f a b g) :
    ModuleHomotopy.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom) ⥤
      RingedSite.Hom.ModuleSections.Derived.{u}
        (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom) :=
  moduleGlobalSectionsToModuleDerived.{u}
      (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom) ⋙
    globalSectionsRestrictionDerived.{u, u, u, u, u, u} (coefficientHom sq)

/-- The homotopy-level target for the specialized global-sections comparison. -/
noncomputable abbrev comparisonTarget (sq : CommSq f a b g) :
    ModuleHomotopy.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom) ⥤
      RingedSite.Hom.ModuleSections.Derived.{u}
        (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom) :=
  (coefficientHom sq).modulePushforward.{u}.mapHomotopyCategory (up ℤ) ⋙
    moduleGlobalSectionsToModuleDerived.{u}
      (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom)

/-- The derived source for the specialized global-sections comparison. -/
noncomputable abbrev comparisonSourceDerived (sq : CommSq f a b g) :
    ModuleDerived.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom) ⥤
      RingedSite.Hom.ModuleSections.Derived.{u}
        (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom) :=
  moduleDerivedGlobalSections.{u}
      (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom) ⋙
    globalSectionsRestrictionDerived.{u, u, u, u, u, u} (coefficientHom sq)

/-- The derived target for the specialized global-sections comparison. -/
noncomputable abbrev comparisonTargetDerived (sq : CommSq f a b g)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (coefficientHom sq))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))] :
    ModuleDerived.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom) ⥤
      RingedSite.Hom.ModuleSections.Derived.{u}
        (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom) :=
  modulePushforwardDerived.{u} (coefficientHom sq) ⋙
    moduleDerivedGlobalSections.{u}
      (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom)

/-- The unit for the source model in the specialized comparison. -/
noncomputable def comparisonSourceUnit (sq : CommSq f a b g) :
    comparisonSource sq ⟶
      moduleLocalization.{u}
          (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom) ⋙
        comparisonSourceDerived sq :=
  Functor.whiskerRight
      (Functor.totalRightDerivedUnit
        (moduleGlobalSectionsToModuleDerived.{u}
          (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))
        (moduleLocalization.{u}
          (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))
        (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom)))
      (globalSectionsRestrictionDerived.{u, u, u, u, u, u} (coefficientHom sq)) ≫
    (Functor.associator
      (moduleLocalization.{u}
        (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))
      (moduleDerivedGlobalSections.{u}
        (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))
      (globalSectionsRestrictionDerived.{u, u, u, u, u, u} (coefficientHom sq))).hom

/-- The unit for the target model in the specialized comparison. -/
noncomputable def comparisonTargetUnit (sq : CommSq f a b g)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (coefficientHom sq))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))] :
    comparisonTarget sq ⟶
      moduleLocalization.{u}
          (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom) ⋙
        comparisonTargetDerived sq :=
  Functor.whiskerLeft
      ((coefficientHom sq).modulePushforward.{u}.mapHomotopyCategory (up ℤ))
      (Functor.totalRightDerivedUnit
        (moduleGlobalSectionsToModuleDerived.{u}
          (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom))
        (moduleLocalization.{u}
          (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom))
        (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom))) ≫
    (Functor.associator
      ((coefficientHom sq).modulePushforward.{u}.mapHomotopyCategory (up ℤ))
      (moduleLocalization.{u}
        (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom))
      (moduleDerivedGlobalSections.{u}
        (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom))).hom ≫
    Functor.whiskerRight
      (Functor.totalRightDerivedUnit
        (modulePushforwardToDerived.{u} (coefficientHom sq))
        (moduleLocalization.{u}
          (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))
        (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom)))
      (moduleDerivedGlobalSections.{u}
        (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom)) ≫
    (Functor.associator
      (moduleLocalization.{u}
        (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))
      (modulePushforwardDerived.{u} (coefficientHom sq))
      (moduleDerivedGlobalSections.{u}
        (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom))).hom

/-- The source comparison unit has the canonical right-derived universal property. -/
noncomputable instance comparisonSourceIsRightDerived
    (sq : CommSq f a b g) :
    (comparisonSourceDerived sq).IsRightDerivedFunctor
      (comparisonSourceUnit sq)
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom)) := sorry

/-- The target comparison unit has the canonical right-derived universal property. -/
noncomputable instance comparisonTargetIsRightDerived
    (sq : CommSq f a b g)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (coefficientHom sq))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))] :
    (comparisonTargetDerived sq).IsRightDerivedFunctor
      (comparisonTargetUnit sq)
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom)) := sorry

/-- The homotopy-level inverse global-sections/direct-image comparison. -/
noncomputable def comparisonNatInv (sq : CommSq f a b g) :
    comparisonTarget sq ⟶ comparisonSource sq :=
  -- Local instance justification (proof-local temporary data): source global-sections additivity is required by the homotopy comparison.
  letI : (moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom)).Additive :=
    moduleGlobalSectionsFunctor_additive
      (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom)
  -- Local instance justification (proof-local temporary data): target global-sections additivity is required by the homotopy comparison.
  letI : (moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom)).Additive :=
    moduleGlobalSectionsFunctor_additive
      (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom)
  (Functor.associator
      ((coefficientHom sq).modulePushforward.{u}.mapHomotopyCategory (up ℤ))
      ((moduleGlobalSectionsFunctor.{u}
        (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom)).mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh : HomotopyCategory
        (_root_.ModuleCat.{u} (coefficientRing b)) (up ℤ) ⥤ coefficientDerived b)).inv ≫
    Functor.whiskerRight
      ((Functor.mapHomotopyCategoryCompIso
        (Iso.refl ((coefficientHom sq).modulePushforward.{u} ⋙
          moduleGlobalSectionsFunctor.{u}
            (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom))) (up ℤ)).hom)
      (DerivedCategory.Qh : HomotopyCategory
        (_root_.ModuleCat.{u} (coefficientRing b)) (up ℤ) ⥤ coefficientDerived b) ≫
    Functor.whiskerRight
      (NatTrans.mapHomotopyCategory
        (RingedSite.Hom.ModuleSections.moduleGlobalSectionsPushforwardNatIso.{u}
          (coefficientHom sq)).inv (up ℤ))
      (DerivedCategory.Qh : HomotopyCategory
        (_root_.ModuleCat.{u} (coefficientRing b)) (up ℤ) ⥤ coefficientDerived b) ≫
    Functor.whiskerRight
      ((Functor.mapHomotopyCategoryCompIso
        (Iso.refl (moduleGlobalSectionsFunctor.{u}
          (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom) ⋙
            (globalSectionsRestriction.{u, u, u, u, u, u} (coefficientHom sq) :
              _root_.ModuleCat.{u} (coefficientRing a) ⥤
                _root_.ModuleCat.{u} (coefficientRing b)))) (up ℤ)).inv)
      (DerivedCategory.Qh : HomotopyCategory
        (_root_.ModuleCat.{u} (coefficientRing b)) (up ℤ) ⥤ coefficientDerived b) ≫
    (Functor.associator
      ((moduleGlobalSectionsFunctor.{u}
        (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom)).mapHomotopyCategory (up ℤ))
      ((globalSectionsRestriction.{u, u, u, u, u, u}
        (coefficientHom sq)).mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh : HomotopyCategory
        (_root_.ModuleCat.{u} (coefficientRing b)) (up ℤ) ⥤ coefficientDerived b)).hom ≫
    Functor.whiskerLeft
      ((moduleGlobalSectionsFunctor.{u}
        (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom)).mapHomotopyCategory (up ℤ))
      ((globalSectionsRestriction.{u, u, u, u, u, u}
        (coefficientHom sq)).mapDerivedCategoryFactorsh.inv) ≫
    (Functor.associator
      ((moduleGlobalSectionsFunctor.{u}
        (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom)).mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh : HomotopyCategory
        (_root_.ModuleCat.{u} (coefficientRing a)) (up ℤ) ⥤ coefficientDerived a)
      (globalSectionsRestrictionDerived.{u, u, u, u, u, u} (coefficientHom sq))).inv

/-- The specialized derived global-sections comparison in the pullback direction. -/
noncomputable def derivedGlobalComparisonInv (sq : CommSq f a b g)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (coefficientHom sq))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))] :
    comparisonTargetDerived sq ⟶ comparisonSourceDerived sq :=
  Functor.rightDerivedNatTrans
    (comparisonTargetDerived sq) (comparisonSourceDerived sq)
    (comparisonTargetUnit sq) (comparisonSourceUnit sq)
    (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))
    (comparisonNatInv sq)

/-- The derived global-sections pullback, with scalars restricted along the coefficient map. -/
noncomputable def derivedGlobalPullback (sq : CommSq f a b g)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (coefficientHom sq))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))] :
    globalDerivedObject b ⟶
      (globalSectionsRestrictionDerived.{u, u, u, u, u, u}
        (coefficientHom sq)).obj
        (globalDerivedObject a) :=
  (moduleDerivedGlobalSections.{u}
      (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom)).map
      (derivedPullback sq) ≫
    (derivedGlobalComparisonInv sq).app (DerivedPushforward.derivedComplex a)

/-- The derived global pullback is the de Rham pullback followed by inverse global-sections
naturality. -/
theorem derivedGlobalPullback_spec (sq : CommSq f a b g)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (coefficientHom sq))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))] :
    derivedGlobalPullback sq =
      (moduleDerivedGlobalSections.{u}
        (RingedSpace.DeRham.coefficientSite b.toLRSHom.toShHom)).map
          (derivedPullback sq) ≫
        (derivedGlobalComparisonInv sq).app (DerivedPushforward.derivedComplex a) := sorry

/-- Pullback on relative de Rham cohomology, linear over the coefficient ring of the target. -/
noncomputable def restrictedPullback (sq : CommSq f a b g) (q : ℤ)
    [hPull : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (coefficientHom sq))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))] :
    cohomology b q ⟶ restricted sq q :=
  (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (coefficientRing b)) q).map (derivedGlobalPullback sq) ≫
    (Functor.MapDerivedCategory.homologyIso
      (globalSectionsRestriction.{u, u, u, u, u, u} (coefficientHom sq))
      (globalDerivedObject a) q).hom

/-- Restricted pullback is obtained by applying homology to the derived pullback and then using exactness
of restriction of scalars. -/
theorem restrictedPullback_spec (sq : CommSq f a b g) (q : ℤ)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (coefficientHom sq))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))] :
    restrictedPullback sq q =
      (DerivedCategory.homologyFunctor
        (ModuleCat.{u} (coefficientRing b)) q).map (derivedGlobalPullback sq) ≫
        (Functor.MapDerivedCategory.homologyIso
          (globalSectionsRestriction.{u, u, u, u, u, u} (coefficientHom sq))
          (globalDerivedObject a) q).hom := sorry

/-- Pullback on relative de Rham cohomology for a commutative triangle over a common base. -/
noncomputable def pullback {b : Y ⟶ S} (sq : CommSq f a b (𝟙 S)) (q : ℤ)
    [IsAffine S]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (coefficientHom sq))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))] :
    overBase b q ⟶ overBase a q :=
  ModuleCat.ofHom (R := Scheme.globalSectionsRing S)
    (X := overBase b q) (Y := overBase a q)
    { toFun := fun x ↦ (restrictedPullback sq q).hom x
      map_add' := sorry
      map_smul' := sorry }

/-- Base-linear pullback has the same underlying function as coefficient-linear pullback. -/
theorem pullback_spec {b : Y ⟶ S} (sq : CommSq f a b (𝟙 S)) (q : ℤ)
    [IsAffine S]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (coefficientHom sq))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))] :
    ∀ x, (pullback sq q).hom x = (restrictedPullback sq q).hom x := sorry

end AlgebraicGeometry.Scheme.DeRham.Cohomology
