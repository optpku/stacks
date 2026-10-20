module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.AmbientBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.AmbientSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ResidualInvariants
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Basic
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat Opposite
open CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace AlgebraicGeometry.SchemeOverField.AmbientGeometry
open AlgebraicGeometry.Scheme.AmbientAssociatedSheaf
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension F]

/-- The actual inverse-image functor on module sheaves. -/
def modulePullback {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ) Z.smallEtaleTopology Y.smallEtaleTopology

/-- Module-sheaf pullback composition is fixed by the actual adjunction and site pullback compositor. -/
def modulePullbackComp {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B) :
    modulePullback Λ p ⋙ modulePullback Λ q ≅ modulePullback Λ (q ≫ p) :=
  let siteIso : smallEtalePullback p ⋙ smallEtalePullback q ≅ smallEtalePullback (q ≫ p) :=
    (MorphismProperty.Over.pullbackComp q p).symm
  Adjunction.leftAdjointCompIso
    (smallEtalePullback_sheafAdjunction p (ModuleCat.{u + 1} Λ))
    (smallEtalePullback_sheafAdjunction q (ModuleCat.{u + 1} Λ))
    (smallEtalePullback_sheafAdjunction (q ≫ p) (ModuleCat.{u + 1} Λ))
    (sheafPushforwardContinuousComp' siteIso (ModuleCat.{u + 1} Λ)
      A.smallEtaleTopology B.smallEtaleTopology C.smallEtaleTopology)

/-- Pullback of sections uses the geometric adjunction unit and the identity-object pullback iso. -/
def sectionsPullback {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    sections (X := Z) Λ ⟶ modulePullback Λ f ⋙ sections (X := Y) Λ where
  app F :=
    ((sheafToPresheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
      ((smallEtalePullback_sheafAdjunction f (ModuleCat.{u + 1} Λ)).unit.app F)).app
        (op (AlgebraicGeometry.Scheme.Etale.globalEtale Z)) ≫
      ((modulePullback Λ f).obj F).obj.map (op (AlgebraicGeometry.Scheme.Etale.globalEtalePullbackIso f).inv)
  naturality := sorry

variable {k : Type u} [Field k] (X : SchemeOverField k)

/-- Galois descent of a geometrically pulled-back sheaf uses the actual
pullback compositor and equality of the structural maps over X. -/
def galoisDescentIso (σ : Gal(AlgebraicClosure k/k))
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (modulePullback Λ (FieldExtension.Galois.map k (AlgebraicClosure k) X.hom σ)).obj
        ((modulePullback Λ (geometricToArithmeticHom X)).obj F) ≅
      (modulePullback Λ (geometricToArithmeticHom X)).obj F :=
  (modulePullbackComp Λ (geometricToArithmeticHom X)
      (FieldExtension.Galois.map k (AlgebraicClosure k) X.hom σ)).app F ≪≫
    (eqToIso (congrArg (fun h ↦ modulePullback Λ h)
      (FieldExtension.Galois.map_toSource k (AlgebraicClosure k) X.hom σ))).app F

/-- The geometric Galois action on sections is defined before any comparison with invariants. -/
def geometricSectionsEnd (σ : Gal(AlgebraicClosure k/k))
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (sections Λ).obj ((modulePullback Λ (geometricToArithmeticHom X)).obj F) ⟶
      (sections Λ).obj ((modulePullback Λ (geometricToArithmeticHom X)).obj F) :=
  (sectionsPullback Λ (FieldExtension.Galois.map k (AlgebraicClosure k) X.hom σ)).app
      ((modulePullback Λ (geometricToArithmeticHom X)).obj F) ≫
    (sections Λ).map (galoisDescentIso Λ X σ F).hom

/-- Identity acts identically on the actual geometric section module. -/
theorem geometricSectionsEnd_one
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    geometricSectionsEnd Λ X 1 F = 𝟙 _ := sorry

/-- The geometric section endomorphisms respect Galois multiplication. -/
theorem geometricSectionsEnd_mul (σ τ : Gal(AlgebraicClosure k/k))
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    geometricSectionsEnd Λ X (σ * τ) F =
      geometricSectionsEnd Λ X τ F ≫ geometricSectionsEnd Λ X σ F := sorry

variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (ηbar : GeometricPoint (geometricBaseChange X))
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [∀ U : (geometricBaseChange X).Etale,
    HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]

/-- The two induced fundamental-group maps use the same corrected projection/lift fiber comparison. -/
theorem geometricFundamentalMap_eq :
    AlgebraicGeometry.Scheme.GeometricPoint.fundamentalGroupMap (geometricToArithmeticHom X) ηbar = (geometricToArithmetic X ηbar).hom := sorry

/-- The generic restriction/invariants functor is the existing geometric invariants functor. -/
def geometricInvariantsRestrictionIso :
    restriction Λ (geometricToArithmeticHom X) ηbar ⋙
        CategoryTheory.Action.ModuleCat.DiscreteModuleCat.fixedPointsFunctor Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)) ≅
      Ambient.invariants Λ X ηbar :=
  eqToIso (congrArg
    (fun φ ↦ discreteModuleRes (R := Λ) φ ⋙
      CategoryTheory.Action.ModuleCat.DiscreteModuleCat.fixedPointsFunctor Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)))
    (geometricFundamentalMap_eq X ηbar))

/-- Geometric sections of the actual arithmetic associated sheaf, on all discrete coefficients. -/
def geometricSections :
    DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar))) ⥤
      ModuleCat.{u + 1} Λ :=
  (functor (Λ := Λ) (xbar := arithmeticPoint X ηbar) ⋙
    modulePullback Λ (geometricToArithmeticHom X)) ⋙ sections Λ

/-- The natural geometric sections/invariants comparison uses actual sheaf base change,
then the germ comparison on the geometric scheme. -/
def geometricSectionsIso : geometricSections Λ X ηbar ≅ Ambient.invariants Λ X ηbar :=
  Functor.isoWhiskerRight (baseChangeNatIso Λ (geometricToArithmeticHom X) ηbar) (sections Λ) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (restriction Λ (geometricToArithmeticHom X) ηbar) (sectionsIso Λ ηbar) ≪≫
    geometricInvariantsRestrictionIso Λ X ηbar

/-- Geometric sections carry the independently constructed Galois pullback action. -/
def geometricSectionsAction
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))) :
    Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k) where
  V := (geometricSections Λ X ηbar).obj M
  ρ := { toFun := fun σ ↦ geometricSectionsEnd Λ X σ (obj M)
         map_one' := geometricSectionsEnd_one Λ X (obj M)
         map_mul' := fun σ τ ↦ geometricSectionsEnd_mul Λ X σ τ (obj M) }

/-- The actual section-germ comparison intertwines geometric Galois pullback with
arithmetic translation on invariant vectors, independently of the chosen lift. -/
theorem geometricSectionsIso_equivariant
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar))))
    (σ : Gal(AlgebraicClosure k/k)) :
    (geometricSectionsAction Λ X ηbar M).ρ σ ≫ (geometricSectionsIso Λ X ηbar).hom.app M =
      (geometricSectionsIso Λ X ηbar).hom.app M ≫ (Ambient.residualInvariants Λ X ηbar M).ρ σ := sorry

/-- The equivariant geometric sections/invariants isomorphism retains the specified maps. -/
def geometricSectionsResidualIso
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))) :
    geometricSectionsAction Λ X ηbar M ≅ Ambient.residualInvariants Λ X ηbar M :=
  Action.mkIso ((geometricSectionsIso Λ X ηbar).app M) (geometricSectionsIso_equivariant Λ X ηbar M)

/-- The geometric Galois action is natural for coefficient morphisms, through geometric pullback. -/
theorem geometricSectionsAction_naturality
    {M N : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))}
    (a : M ⟶ N) (σ : Gal(AlgebraicClosure k/k)) :
    (geometricSectionsAction Λ X ηbar M).ρ σ ≫ (geometricSections Λ X ηbar).map a =
      (geometricSections Λ X ηbar).map a ≫ (geometricSectionsAction Λ X ηbar N).ρ σ := sorry

/-- The residual geometric sections functor retains the actual section maps on morphisms. -/
def geometricSectionsActionFunctor :
    DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar))) ⥤
      Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k) where
  obj := geometricSectionsAction Λ X ηbar
  map a := { hom := (geometricSections Λ X ηbar).map a
             comm := geometricSectionsAction_naturality Λ X ηbar a }
  map_id := sorry
  map_comp := sorry

/-- The residual invariants functor restricts the original coefficient maps to fixed vectors. -/
def residualInvariantsFunctor :
    DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar))) ⥤
      Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k) where
  obj := Ambient.residualInvariants Λ X ηbar
  map a := { hom := (Ambient.invariants Λ X ηbar).map a
             comm := fun _ ↦ sorry }
  map_id := sorry
  map_comp := sorry

/-- The sections/invariants comparison is natural as an isomorphism of residual Galois modules. -/
def geometricSectionsResidualNatIso :
    geometricSectionsActionFunctor Λ X ηbar ≅ residualInvariantsFunctor Λ X ηbar :=
  NatIso.ofComponents (geometricSectionsResidualIso Λ X ηbar) (fun _ ↦ sorry)

/-- Compatibility names any arithmetic lift with the prescribed Galois image;
the geometric section action therefore does not depend on the selected lift. -/
theorem geometricSectionsResidual_lift
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar))))
    (σ : Gal(AlgebraicClosure k/k))
    (a : Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))
    (ha : arithmeticToGalois X (arithmeticPoint X ηbar) a = galoisToGaloisPoint X ηbar σ)
    (s : (geometricSections Λ X ηbar).obj M) :
    (((geometricSectionsIso Λ X ηbar).hom.app M).hom
      (((geometricSectionsAction Λ X ηbar M).ρ σ).hom s)).val =
        (M.obj.ρ a).hom ((((geometricSectionsIso Λ X ηbar).hom.app M).hom s).val) := sorry

end AlgebraicGeometry.SchemeOverField.AmbientGeometry
