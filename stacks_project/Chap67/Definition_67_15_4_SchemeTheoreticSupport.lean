module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTheoreticSupport

/-!
# Scheme-theoretic support of a finite-type quasi-coherent module

The shared owners provide the annihilator ideal and the closed subspace it cuts
out, together with the least-support characterization.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.schemeTheoreticSupport :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType], ClosedSubspace X)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.annihilatorSectionIdeal :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    (U : (smallEtaleSite X)ᵒᵖ), Ideal ((structureSheaf X).obj.obj U))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.annihilatorSheaf :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules), X.Modules)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.annihilatorι :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules),
    annihilatorSheaf F ⟶ SheafOfModules.unit (structureSheaf X))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.annihilatorIdeal :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules), IdealSubobject X)
