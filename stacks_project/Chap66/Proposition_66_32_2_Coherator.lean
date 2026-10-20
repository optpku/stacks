module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Coherator

/-!
# Coherators for quasi-coherent modules on algebraic spaces

The inclusion of quasi-coherent modules into all module sheaves on an algebraic space admits a
chosen right adjoint, the coherator. This module records the adjunction and its additive
structure.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.coherator :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), X.Modules ⥤ QCoh X)

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.coheratorAdjunction :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), QCoh.inclusion X ⊣ QCoh.coherator X)

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.coherator.additive :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), (QCoh.coherator X).Additive)
