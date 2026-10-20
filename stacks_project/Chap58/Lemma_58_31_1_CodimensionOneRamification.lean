module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.CodimensionOneRamification

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

@[expose] public section

universe u

/- Compatibility checks for the reusable codimension-one finite-etale API. -/
#check (AlgebraicGeometry.Scheme.HasDVRBoundary :
  (X : Scheme.{u}) → X.Opens → Prop)
#check AlgebraicGeometry.Scheme.HasDVRBoundary.spec
#check (AlgebraicGeometry.Scheme.FiniteEtale.genericMap :
  ∀ {X : Scheme.{u}} (Z : AlgebraicGeometry.PrimeDivisor X),
    Spec (CommRingCat.of (FractionRing (X.presheaf.stalk Z.genericPoint))) ⟶ X)
#check (AlgebraicGeometry.Scheme.FiniteEtale.genericMap_spec :
  ∀ {X : Scheme.{u}} (Z : AlgebraicGeometry.PrimeDivisor X),
    AlgebraicGeometry.Scheme.FiniteEtale.genericMap Z =
      Spec.map (CommRingCat.ofHom
          (algebraMap (X.presheaf.stalk Z.genericPoint)
            (FractionRing (X.presheaf.stalk Z.genericPoint)))) ≫
        X.fromSpecStalk Z.genericPoint)
#check (AlgebraicGeometry.Scheme.FiniteEtale.boundaryFiber :
  ∀ {X : Scheme.{u}} {U : X.Opens} (Y : Scheme.FiniteEtale U.toScheme)
    (Z : AlgebraicGeometry.PrimeDivisor X),
    CommAlgCat (FractionRing (X.presheaf.stalk Z.genericPoint)))
#check (AlgebraicGeometry.Scheme.FiniteEtale.boundaryFiber_spec :
  ∀ {X : Scheme.{u}} {U : X.Opens} (Y : Scheme.FiniteEtale U.toScheme)
    (Z : AlgebraicGeometry.PrimeDivisor X),
    AlgebraicGeometry.Scheme.FiniteEtale.boundaryFiber Y Z =
      Scheme.Hom.globalSectionsAlg
        (pullback.snd (Y.hom ≫ U.ι)
          (AlgebraicGeometry.Scheme.FiniteEtale.genericMap Z)))
#check (AlgebraicGeometry.Scheme.FiniteEtale.BoundaryFiber.Branch.ring :
  ∀ {X : Scheme.{u}} {U : X.Opens} (Y : Scheme.FiniteEtale U.toScheme)
    (Z : AlgebraicGeometry.PrimeDivisor X),
    MaximalSpectrum (AlgebraicGeometry.Scheme.FiniteEtale.boundaryFiber Y Z) → Type _)
#check (AlgebraicGeometry.Scheme.FiniteEtale.BoundaryFiber.Branch.field :
  ∀ {X : Scheme.{u}} {U : X.Opens} (Y : Scheme.FiniteEtale U.toScheme)
    (Z : AlgebraicGeometry.PrimeDivisor X)
    (m : MaximalSpectrum (AlgebraicGeometry.Scheme.FiniteEtale.boundaryFiber Y Z)),
    Field (AlgebraicGeometry.Scheme.FiniteEtale.BoundaryFiber.Branch.ring Y Z m))
#check (AlgebraicGeometry.Scheme.FiniteEtale.BoundaryFiber.Branch.fractionAlgebra :
  ∀ {X : Scheme.{u}} {U : X.Opens} (Y : Scheme.FiniteEtale U.toScheme)
    (Z : AlgebraicGeometry.PrimeDivisor X)
    (m : MaximalSpectrum (AlgebraicGeometry.Scheme.FiniteEtale.boundaryFiber Y Z)),
    Algebra (FractionRing (X.presheaf.stalk Z.genericPoint))
      (AlgebraicGeometry.Scheme.FiniteEtale.BoundaryFiber.Branch.ring Y Z m))
#check (AlgebraicGeometry.Scheme.FiniteEtale.BoundaryFiber.Branch.baseAlgebra :
  ∀ {X : Scheme.{u}} {U : X.Opens} (Y : Scheme.FiniteEtale U.toScheme)
    (Z : AlgebraicGeometry.PrimeDivisor X)
    (m : MaximalSpectrum (AlgebraicGeometry.Scheme.FiniteEtale.boundaryFiber Y Z)),
    Algebra (X.presheaf.stalk Z.genericPoint)
      (AlgebraicGeometry.Scheme.FiniteEtale.BoundaryFiber.Branch.ring Y Z m))
#check (AlgebraicGeometry.Scheme.FiniteEtale.BoundaryFiber.Branch.isScalarTower :
  ∀ {X : Scheme.{u}} {U : X.Opens} (Y : Scheme.FiniteEtale U.toScheme)
    (Z : AlgebraicGeometry.PrimeDivisor X)
    (m : MaximalSpectrum (AlgebraicGeometry.Scheme.FiniteEtale.boundaryFiber Y Z)),
    @IsScalarTower (X.presheaf.stalk Z.genericPoint)
      (FractionRing (X.presheaf.stalk Z.genericPoint))
      (AlgebraicGeometry.Scheme.FiniteEtale.BoundaryFiber.Branch.ring Y Z m)
      inferInstance
      (AlgebraicGeometry.Scheme.FiniteEtale.BoundaryFiber.Branch.fractionAlgebra Y Z m).toSMul
      (AlgebraicGeometry.Scheme.FiniteEtale.BoundaryFiber.Branch.baseAlgebra Y Z m).toSMul)
#check AlgebraicGeometry.Scheme.FiniteEtale.BoundaryFiber.Branch.spec
#check AlgebraicGeometry.Scheme.FiniteEtale.unramifiedBranch
#check AlgebraicGeometry.Scheme.FiniteEtale.tameBranch
#check AlgebraicGeometry.Scheme.FiniteEtale.IsUnramifiedInCodimensionOne
#check AlgebraicGeometry.Scheme.FiniteEtale.IsTamelyRamifiedInCodimensionOne
#check AlgebraicGeometry.Scheme.FiniteEtale.isUnramifiedInCodimensionOne_iff
#check AlgebraicGeometry.Scheme.FiniteEtale.isTamelyRamifiedInCodimensionOne_iff
#check AlgebraicGeometry.Scheme.FiniteEtale.IsUnramifiedInCodimensionOne.isTamelyRamified
#check AlgebraicGeometry.Scheme.FiniteEtale.IsUnramifiedInCodimensionOne.baseChange
#check AlgebraicGeometry.Scheme.FiniteEtale.IsTamelyRamifiedInCodimensionOne.baseChange
