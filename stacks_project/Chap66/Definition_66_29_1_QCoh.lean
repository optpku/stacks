module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent
import StacksCheckRecall

/-! # Quasi-coherent modules on an algebraic space

@stack 03G9

The actual object property and its full subcategory are owned by the public library.
-/

@[expose] public section

universe u

/- Definition 66.29.1 (1): a quasi-coherent 𝒪_X-module on an algebraic space X over a scheme S
is a quasi-coherent module on the ringed site (X_étale, 𝒪_X) in the sense of
SheafOfModules.IsQuasicoherent. -/
@[stacks 03G9 "(1) quasi-coherent module"]
#check (AlgebraicGeometry.AlgebraicSpace.quasiCoherentModuleProperty :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    CategoryTheory.ObjectProperty (AlgebraicGeometry.AlgebraicSpace.Modules X))

/- Definition 66.29.1 (2): the category of quasi-coherent sheaves on X is denoted QCoh(𝒪_X). -/
@[stacks 03G9 "(2) category of quasi-coherent modules"]
#check (AlgebraicGeometry.AlgebraicSpace.QCoh :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.quasiCoherentModuleProperty_eq :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    AlgebraicGeometry.AlgebraicSpace.quasiCoherentModuleProperty X =
      SheafOfModules.isQuasicoherent (AlgebraicGeometry.AlgebraicSpace.structureSheaf X))
#check (AlgebraicGeometry.AlgebraicSpace.QCoh.inclusion :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    CategoryTheory.Functor (AlgebraicGeometry.AlgebraicSpace.QCoh X)
      (AlgebraicGeometry.AlgebraicSpace.Modules X))
