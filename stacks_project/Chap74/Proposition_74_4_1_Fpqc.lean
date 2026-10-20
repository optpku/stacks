module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.DescentData.Fpqc

@[expose] public section

universe u v

#check
  (AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.isEffective_of_fpqcCovering :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
      {ι : Type v} {family : ι → CategoryTheory.Over X},
      AlgebraicGeometry.AlgebraicSpace.FpqcCovering family →
        ∀ D : AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData
            (fun i ↦ (family i).left) (fun i ↦ (family i).hom),
          AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.IsEffective D)

#check
  (AlgebraicGeometry.AlgebraicSpace.QCoh.canonicalFunctor.fullyFaithful_of_fpqcCovering :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
      {ι : Type v} {family : ι → CategoryTheory.Over X},
      AlgebraicGeometry.AlgebraicSpace.FpqcCovering family →
        Nonempty
          (AlgebraicGeometry.AlgebraicSpace.QCoh.canonicalFunctor
            (fun i ↦ (family i).left) (fun i ↦ (family i).hom)).FullyFaithful)
