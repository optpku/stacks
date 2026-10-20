module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRingHom

/-! Compatibility facade for actual internal commutative-ring inverse/direct images. -/

open CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.commInverseImageStructureSheafMap :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y),
    AlgebraicGeometry.AlgebraicSpace.commInverseImageStructureSheaf f ⟶
      AlgebraicGeometry.AlgebraicSpace.commStructureSheaf X)
