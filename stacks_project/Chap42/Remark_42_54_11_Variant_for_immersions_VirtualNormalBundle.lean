module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.VirtualNormalBundle

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle :
  ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i], Type (u + 1))
