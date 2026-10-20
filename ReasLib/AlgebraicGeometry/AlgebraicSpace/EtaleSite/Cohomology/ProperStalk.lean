module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.GeometricFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.GeometricPoint.Abelian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Cohomology.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Derived.ProperBaseChange
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.ExactSquare
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Naturality.Iso
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow.Exact.Degree
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Homology

/-!
# Proper stalk comparisons for algebraic spaces

Canonical comparisons identify stalks of higher direct images along proper morphisms
with cohomology of geometric fibres, for torsion sheaves and bounded-below coefficients.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.Sheaf
open CategoryTheory.GrothendieckTopology.Point
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open GeometricPoint

open CategoryTheory.Functor.RightDerived.Composition.BoundedBelow

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Adjunction.Derived.Plus.right` / `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `smallEtaleDerivedBaseChangeHom` and right-derived comparisons.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
variable (f : X ⟶ Y) (ybar : GeometricPoint Y)
variable [(smallEtaleInclusion Y).IsCoverDense (spacesEtaleTopology Y)]
variable [(smallEtaleInclusion X).IsCoverDense (spacesEtaleTopology X)]
variable [(smallEtaleInclusion (ofOver ybar.overObj)).IsCoverDense
    (spacesEtaleTopology (ofOver ybar.overObj))]
variable [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1}]
variable [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1})]
variable [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [HasInjectiveResolutions
    (Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1})]
variable [HasInjectiveResolutions
    (Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{u + 2} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{u + 2} (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{u + 2}
    (Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{u + 2}
    (Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1})]
variable [(sheafPushforwardAbelian f).Additive]
variable [(sheafPushforwardAbelian (geometricFiberToPoint f ybar)).Additive]
variable [(sheafPushforwardAbelian f).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))]
variable [(sheafPushforwardAbelian (geometricFiberToPoint f ybar)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1}))]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} (X := ofOver ybar.overObj) (ybar.hom : ofOver ybar.overObj ⟶ Y)).Additive]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} (geometricFiberToX f ybar)).Additive]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} (X := ofOver ybar.overObj) (ybar.hom : ofOver ybar.overObj ⟶ Y)).PreservesHomology]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} (geometricFiberToX f ybar)).PreservesHomology]
variable [HasColimitsOfSize.{u, u} AddCommGrpCat.{u + 1}]
variable [HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{u + 1}]
variable [HasProducts.{u} AddCommGrpCat.{u + 1}]
variable [HasProducts.{u + 1} AddCommGrpCat.{u + 1}]
variable [InitiallySmall.{u + 1}
    ((etaleBaseChange (X := ofOver ybar.overObj) (ybar.hom : ofOver ybar.overObj ⟶ Y) ⋙
        (toSpacesEtalePoint (idGeometricPoint ybar)).fiber).Elements)]
variable [((etaleBaseChange (X := ofOver ybar.overObj) (ybar.hom : ofOver ybar.overObj ⟶ Y)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (smallEtaleTopology Y) (spacesEtaleTopology (ofOver ybar.overObj))).IsRightAdjoint]
variable [(globalSections (ofOver ybar.overObj)).Additive]
variable [(globalSections (ofOver ybar.overObj)).PreservesHomology]
variable [(globalSections (geometricFiber f ybar)).Additive]
variable [(sheafPushforwardAbelian (geometricFiberToPoint f ybar) ⋙
    globalSections (ofOver ybar.overObj)).Additive]
variable [(globalSections (geometricFiber f ybar)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1}))]
variable [((toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
    Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⥤
      AddCommGrpCat.{u + 1}).Additive]
variable [((toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
    Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⥤
      AddCommGrpCat.{u + 1}).PreservesHomology]
variable [PreservesFiniteLimits
    ((toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
      Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⥤
        AddCommGrpCat.{u + 1})]
variable [PreservesFiniteColimits
    ((toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
      Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⥤
        AddCommGrpCat.{u + 1})]
variable [EnoughInjectives (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [EnoughInjectives
    (Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1})]
variable [EnoughInjectives
    (Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1})]

/-- Global sections on `Spec κ(ȳ)` of a pushforward along the fibre structure morphism
identify with global sections on the geometric fibre. -/
noncomputable def geometricFiberPushforwardSectionsIso :
    sheafPushforwardAbelian (geometricFiberToPoint f ybar) ⋙
        globalSections (ofOver ybar.overObj) ≅
      globalSections (geometricFiber f ybar) := by
  refine
    NatIso.ofComponents
      (fun G ↦ homConstantPushforwardIso (geometricFiberToPoint f ybar) G)
      (fun {_ _} _ ↦ ?_)
  all_goals sorry

/-- Degree-`n` proper base-change comparison of `f` along the geometric fibre square. -/
noncomputable abbrev higherDirectImage_baseChangeHom_geometricFiber
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (n : ℕ) :
    (sheafInverseImage AddCommGrpCat.{u + 1} (X := ofOver ybar.overObj) (ybar.hom : ofOver ybar.overObj ⟶ Y)).obj
        (((sheafPushforwardAbelian f).rightDerived n).obj F) ⟶
      ((sheafPushforwardAbelian (geometricFiberToPoint f ybar)).rightDerived n).obj
        (geometricFiberAbelianSheaf f ybar F) :=
  Functor.RightDerived.exactSquareApp
    (sheafPushforwardAbelian f)
    (sheafPushforwardAbelian (geometricFiberToPoint f ybar))
    (sheafInverseImage AddCommGrpCat.{u + 1} (geometricFiberToX f ybar))
    (sheafInverseImage AddCommGrpCat.{u + 1} (X := ofOver ybar.overObj) (ybar.hom : ofOver ybar.overObj ⟶ Y))
    (smallEtaleAbelianBaseChange f (ybar.hom : ofOver ybar.overObj ⟶ Y)
      (geometricFiberToPoint f ybar) (geometricFiberToX f ybar)
      (geometricFiber_isPullback f ybar)) n F

/-- Canonical comparison `(R^n f_* F)_ȳ ⟶ H^n_étale(X_ȳ, F_ȳ)` of abelian groups. -/
noncomputable def higherDirectImageStalkToGeometricFiberCohomology
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (n : ℕ) :
    (toSmallEtalePoint ybar).sheafFiber.obj
        (((sheafPushforwardAbelian f).rightDerived n).obj F) ⟶
      etaleCohomology (geometricFiber f ybar) (geometricFiberAbelianSheaf f ybar F) n :=
  (abelianStalkPullbackIso ybar
      (((sheafPushforwardAbelian f).rightDerived n).obj F)).hom ≫
    (toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
      (higherDirectImage_baseChangeHom_geometricFiber f ybar F n) ≫
    (uniquePointSheafFiberIsoSections ybar).hom.app
      (((sheafPushforwardAbelian (geometricFiberToPoint f ybar)).rightDerived n).obj
        (geometricFiberAbelianSheaf f ybar F)) ≫
    (Functor.RightDerived.postcompIso
        (sheafPushforwardAbelian (geometricFiberToPoint f ybar))
        (globalSections (ofOver ybar.overObj)) n).inv.app
      (geometricFiberAbelianSheaf f ybar F) ≫
    (NatIso.rightDerived (geometricFiberPushforwardSectionsIso f ybar) n).hom.app
      (geometricFiberAbelianSheaf f ybar F)

/-- `higherDirectImageStalkToGeometricFiberCohomology` is the composite of abelian
stalk-pullback, the degree-`n` proper base-change comparison on `ȳ ×_Y X`, and the
unique-point identification of `R^n f'_*` with étale cohomology of the fibre. -/
theorem higherDirectImageStalkToGeometricFiberCohomology_eq
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (n : ℕ) :
    higherDirectImageStalkToGeometricFiberCohomology f ybar F n =
      (abelianStalkPullbackIso ybar
          (((sheafPushforwardAbelian f).rightDerived n).obj F)).hom ≫
        (toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
          (higherDirectImage_baseChangeHom_geometricFiber f ybar F n) ≫
        (uniquePointSheafFiberIsoSections ybar).hom.app
          (((sheafPushforwardAbelian (geometricFiberToPoint f ybar)).rightDerived n).obj
            (geometricFiberAbelianSheaf f ybar F)) ≫
        (Functor.RightDerived.postcompIso
            (sheafPushforwardAbelian (geometricFiberToPoint f ybar))
            (globalSections (ofOver ybar.overObj)) n).inv.app
          (geometricFiberAbelianSheaf f ybar F) ≫
        (NatIso.rightDerived (geometricFiberPushforwardSectionsIso f ybar) n).hom.app
          (geometricFiberAbelianSheaf f ybar F) :=
  rfl

/-- Identification of the unique-point fibre of derived pushforward homology with étale
cohomology of a bounded-below complex on the geometric fibre. -/
noncomputable def derivedUniquePointHomologyIsoFibreCohomology
    (E' : DerivedCategory.Plus
      (Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1}))
    (n : ℤ) :
    (toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.obj
        ((DerivedCategory.Plus.homologyFunctor
            (Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1}) n).obj
          ((smallEtaleDerivedPushforward (geometricFiberToPoint f ybar)).obj E')) ≅
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        (DerivedCategory.Plus.ι.obj
          ((Functor.RightDerived.Bounded.functor
              (globalSections (geometricFiber f ybar))).obj E')) :=
  (ExactFunctor.Derived.Plus.homologyIso
      (ExactFunctor.of
        ((toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
          Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⥤
            AddCommGrpCat.{u + 1}))
      ((smallEtaleDerivedPushforward (geometricFiberToPoint f ybar)).obj E') n).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} n).mapIso
      ((ExactSecond.iso (sheafPushforwardAbelian (geometricFiberToPoint f ybar))
          (ExactFunctor.of
            ((toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
              Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⥤
                AddCommGrpCat.{u + 1}))).app E') ≪≫
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} n).mapIso
      ((Functor.RightDerived.Bounded.mapIso
          (Functor.isoWhiskerLeft (sheafPushforwardAbelian (geometricFiberToPoint f ybar))
              (uniquePointSheafFiberIsoSections ybar) ≪≫
            geometricFiberPushforwardSectionsIso f ybar)).app E')

/-- Canonical comparison `(R^n f_* E)_ȳ ⟶ H^n_étale(X_ȳ, E_ȳ)` of abelian groups. -/
noncomputable def derivedHigherDirectImageStalkToGeometricFiberCohomology
    (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
    (n : ℤ) :
    (toSmallEtalePoint ybar).sheafFiber.obj
        ((DerivedCategory.homologyFunctor
            (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) n).obj
          (DerivedCategory.Plus.ι.obj ((smallEtaleDerivedPushforward f).obj E))) ⟶
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        (DerivedCategory.Plus.ι.obj
          ((Functor.RightDerived.Bounded.functor
              (globalSections (geometricFiber f ybar))).obj
            (geometricFiberDerived f ybar E))) :=
  (abelianStalkPullbackIso ybar
      ((DerivedCategory.homologyFunctor
          (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) n).obj
        (DerivedCategory.Plus.ι.obj ((smallEtaleDerivedPushforward f).obj E)))).hom ≫
    (toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
      ((ExactFunctor.Derived.Plus.homologyIso (smallEtaleInverseExact (A := ofOver ybar.overObj) (B := Y) (ybar.hom : ofOver ybar.overObj ⟶ Y))
          ((smallEtaleDerivedPushforward f).obj E) n).inv) ≫
    (toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
      ((DerivedCategory.Plus.homologyFunctor
          (Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1}) n).map
        (smallEtaleDerivedBaseChangeHom (X' := geometricFiber f ybar) (Y' := ofOver ybar.overObj) f (ybar.hom : ofOver ybar.overObj ⟶ Y)
          (geometricFiberToPoint f ybar) (geometricFiberToX f ybar)
          (geometricFiber_isPullback f ybar) E)) ≫
    (derivedUniquePointHomologyIsoFibreCohomology f ybar
        (geometricFiberDerived f ybar E) n).hom

/-- `derivedHigherDirectImageStalkToGeometricFiberCohomology` is assembled from abelian
stalk-pullback, derived proper base change, and derived fibre sections. -/
theorem derivedHigherDirectImageStalkToGeometricFiberCohomology_eq
    (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
    (n : ℤ) :
    derivedHigherDirectImageStalkToGeometricFiberCohomology f ybar E n =
      (abelianStalkPullbackIso ybar
          ((DerivedCategory.homologyFunctor
              (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) n).obj
            (DerivedCategory.Plus.ι.obj ((smallEtaleDerivedPushforward f).obj E)))).hom ≫
        (toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
          ((ExactFunctor.Derived.Plus.homologyIso (smallEtaleInverseExact (A := ofOver ybar.overObj) (B := Y) (ybar.hom : ofOver ybar.overObj ⟶ Y))
              ((smallEtaleDerivedPushforward f).obj E) n).inv) ≫
        (toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
          ((DerivedCategory.Plus.homologyFunctor
              (Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1})
              n).map
            (smallEtaleDerivedBaseChangeHom (X' := geometricFiber f ybar) (Y' := ofOver ybar.overObj) f (ybar.hom : ofOver ybar.overObj ⟶ Y)
              (geometricFiberToPoint f ybar) (geometricFiberToX f ybar)
              (geometricFiber_isPullback f ybar) E)) ≫
        (derivedUniquePointHomologyIsoFibreCohomology f ybar
            (geometricFiberDerived f ybar E) n).hom :=
  rfl
/-- If `f : X ⟶ Y` is a proper morphism of algebraic spaces over a
scheme `S` and `ȳ → Y` is a geometric point, then for a torsion abelian sheaf `F` on
`X_étale` the stalk `(R^n f_* F)_ȳ` is canonically isomorphic to étale cohomology
`H^n_étale(X_ȳ, F_ȳ)` of the geometric fibre `X_ȳ = ȳ ×_Y X`, where `F_ȳ` is the
inverse image of `F` to that fibre. -/
theorem higherDirectImage_stalk_eq_geometricFiberCohomology
    [Proper f] (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (hF : IsLocallyTorsion F) (n : ℕ) :
    IsIso (higherDirectImageStalkToGeometricFiberCohomology f ybar F n) :=
  sorry

/-- If `f : X ⟶ Y` is a proper morphism of algebraic spaces over a
scheme `S` and `ȳ → Y` is a geometric point, then for `E ∈ D⁺(X_étale)` with torsion
cohomology sheaves the stalk `(R^n f_* E)_ȳ` is canonically isomorphic to étale
cohomology `H^n_étale(X_ȳ, E_ȳ)` of the geometric fibre, where `E_ȳ` is the inverse
image of `E` to `X_ȳ = ȳ ×_Y X`. -/
theorem derivedHigherDirectImage_stalk_eq_geometricFiberCohomology
    [Proper f] (E : DerivedCategory.Plus
      (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) E)
    (n : ℤ) :
    IsIso (derivedHigherDirectImageStalkToGeometricFiberCohomology f ybar E n) :=
  sorry

/-- The canonical stalk-to-fibre comparison is invertible for a proper morphism
and a locally torsion abelian sheaf supplied as a fact. -/
instance higherDirectImageStalkToGeometricFiberCohomology_isIso
    [Proper f] (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [hF : Fact (IsLocallyTorsion F)] (n : ℕ) :
    IsIso (higherDirectImageStalkToGeometricFiberCohomology f ybar F n) :=
  higherDirectImage_stalk_eq_geometricFiberCohomology f ybar F hF.out n

/-- The canonical derived stalk-to-fibre comparison is invertible for a proper
morphism and a bounded-below object whose locally torsion cohomology is supplied as a fact. -/
instance derivedHigherDirectImageStalkToGeometricFiberCohomology_isIso
    [Proper f] (E : DerivedCategory.Plus
      (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
    [hE : Fact (DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) E)]
    (n : ℤ) :
    IsIso (derivedHigherDirectImageStalkToGeometricFiberCohomology f ybar E n) :=
  derivedHigherDirectImage_stalk_eq_geometricFiberCohomology f ybar E hE.out n

end AlgebraicGeometry.AlgebraicSpace
