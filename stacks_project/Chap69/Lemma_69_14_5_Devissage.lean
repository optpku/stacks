module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Devissage

/-!
# Dévissage of coherent modules on algebraic spaces

The coherent-module dévissage owner provides extension closure, finite-coproduct
descent, and the reduced closed model criterion.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.DevissageShortExactClosed :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (P : X.Modules → Prop), Prop)
