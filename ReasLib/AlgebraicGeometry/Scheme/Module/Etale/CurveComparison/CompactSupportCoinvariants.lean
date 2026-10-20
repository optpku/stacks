module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.CompactSupport.Galois
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricCoinvariantsQuotient
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.AssociatedSheaf

/-!
# Compactly supported cohomology and geometric coinvariants

The maximal geometrically constant quotient induces the degree-two compact-support
comparison. On smooth geometrically connected curves it identifies cohomology with
the geometric coinvariants equipped with the inverse cyclotomic twist.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Action.ModuleCat
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.SchemeOverField
open CategoryTheory.ObjectProperty
open scoped AlgebraicGeometry MonoidAlgebra

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.left.Etale,
    HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [X.left.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]
variable (xbar : GeometricPoint (geometricBaseChange X))
variable (Mρ : (finiteTypeDiscreteModule Λ
    (Aut (GeometricPoint.finiteFiber (arithmeticPoint X xbar)))).FullSubcategory)
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)

/-- The sheaf morphism `F_ρ ⟶ F''` onto the maximal geometrically constant quotient,
associated to inflation of geometric coinvariants. -/
def geometricallyConstantQuotient :
    associatedSheaf Λ (arithmeticPoint X xbar) Mρ ⟶
      associatedSheaf Λ (arithmeticPoint X xbar)
        (inflationOfGeometricCoinvariants X xbar Mρ) :=
  ((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ
      (arithmeticPoint X xbar)).inverse.map
    (homMk (homMk (coinvariantsQuotientHom X xbar Mρ)))).hom

/-- Compactly supported cohomology of the geometrically constant quotient, as a Galois module. -/
def cohomologyCompactSupportConstantQuotient :
    Action AddCommGrpCat.{u + 1} Gal(AlgebraicClosure k/k) :=
  cohomologyCompactSupportGaloisModule X P
    ((sheafCompose X.left.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
      (associatedSheaf Λ (arithmeticPoint X xbar)
        (inflationOfGeometricCoinvariants X xbar Mρ)))
    2

/-- The comparison morphism on compactly supported cohomology induced by
`geometricallyConstantQuotient`. -/
def compactSupportToCoinvariants :
    cohomologyCompactSupportGaloisModule X P
        ((sheafCompose X.left.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          (associatedSheaf Λ (arithmeticPoint X xbar) Mρ)) 2 ⟶
      cohomologyCompactSupportConstantQuotient X xbar Mρ P where
  hom :=
    let Ybar := P.obj.right
    etaleCohomologyMap₁
      ((etaleAbelianSheafPullback₁
          (FieldExtension.toSource k (AlgebraicClosure k) Ybar.hom)).map
        ((etaleExtensionByZero (Compactification.Of.ι P) AddCommGrpCat.{u + 1}).map
          ((sheafCompose X.left.smallEtaleTopology
              (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
            (geometricallyConstantQuotient X xbar Mρ))))
      2
  comm := fun _ ↦ sorry

/-- The comparison morphism intertwines the Galois action on compactly supported cohomology
with the residual action on the geometrically constant quotient. -/
theorem compactSupportToCoinvariants_equivariant
    (σ : Gal(AlgebraicClosure k/k)) :
    (cohomologyCompactSupportGaloisModule X P
          ((sheafCompose X.left.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            (associatedSheaf Λ (arithmeticPoint X xbar) Mρ)) 2).ρ σ ≫
        (compactSupportToCoinvariants X xbar Mρ P).hom =
      (compactSupportToCoinvariants X xbar Mρ P).hom ≫
        (cohomologyCompactSupportConstantQuotient X xbar Mρ P).ρ σ :=
  (compactSupportToCoinvariants X xbar Mρ P).comm σ

/-- For a smooth geometrically connected curve with invertible finite coefficients,
the maximal geometrically constant quotient induces a bijection on degree-two
compactly supported geometric cohomology. -/
theorem compactSupportToCoinvariants_bijective
    {k : Type u} [Field k] {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]
    (X : SchemeOverField k) [Curve X] [Smooth X.hom] [GeometricallyConnected X.hom]
    [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.left.Etale,
      HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [X.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]
    (xbar : GeometricPoint (geometricBaseChange X))
    (Mρ : (finiteTypeDiscreteModule Λ
      (Aut (GeometricPoint.finiteFiber (arithmeticPoint X xbar)))).FullSubcategory)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    (hΛ : IsUnit (Nat.card Λ : k)) :
    Function.Bijective (compactSupportToCoinvariants X xbar Mρ P).hom :=
  sorry

/-- Degree-two compactly supported geometric cohomology of the sheaf associated to a
finite arithmetic module is isomorphic to its geometric coinvariants with inverse
cyclotomic twist, as an absolute Galois module. -/
theorem compactSupport_iso_geometricCoinvariantsTateTwist
    {k : Type u} [Field k] {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]
    (X : SchemeOverField k) [Curve X] [Smooth X.hom] [GeometricallyConnected X.hom]
    [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
    [ConnectedSpace (Spec (CommRingCat.of k))]
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.left.Etale,
      HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [X.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]
    (xbar : GeometricPoint (geometricBaseChange X))
    (Mρ : (finiteTypeDiscreteModule Λ
      (Aut (GeometricPoint.finiteFiber (arithmeticPoint X xbar)))).FullSubcategory)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    (hΛ : IsUnit (Nat.card Λ : k)) :
    IsIsomorphic
      (cohomologyCompactSupportGaloisModule X P
        ((sheafCompose X.left.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            (associatedSheaf Λ (arithmeticPoint X xbar) Mρ)) 2)
      (((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapAction
          Gal(AlgebraicClosure k/k)).obj
        (tateTwist hΛ (geometricCoinvariants X xbar Mρ.obj))) :=
  sorry

end AlgebraicGeometry.SchemeOverField

end
