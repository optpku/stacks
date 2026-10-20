module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ideal.Torsion

/-!
# Ideal-torsion subsheaves and their inclusions

The subsheaf and inclusion are supplied by the shared ideal-torsion owner.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

#check (AlgebraicGeometry.AlgebraicSpace.Modules.idealTorsionSubsheaf :
  IdealSubobject X → X.Modules → X.Modules)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.idealTorsionSubsheafι :
  ∀ (I : IdealSubobject X) (ℱ : X.Modules),
    AlgebraicGeometry.AlgebraicSpace.Modules.idealTorsionSubsheaf I ℱ ⟶ ℱ)
