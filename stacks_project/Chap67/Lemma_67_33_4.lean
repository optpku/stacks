module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ResidueFieldTrdeg.Jacobson

/-!
# Residue-field transcendence degree of finite-type points over Jacobson targets

A locally finite-type morphism of algebraic spaces into an étale-locally
Jacobson target has residue-field transcendence degree 0 at finite-type points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 67.33.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is locally of finite type, `Y` is Jacobson
in the étale-local sense, and `x` is a finite-type point of `X`,
then `residueFieldTrdegAt f x = 0`. -/
@[stacks 0ECY] #check
  (AlgebraicGeometry.AlgebraicSpace.residueFieldTrdegAt.eq_zero_of_isFiniteTypePoint :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFiniteType f] [IsJacobson Y] {x : Points X},
      IsFiniteTypePoint x → residueFieldTrdegAt f x = 0)

#check
  (AlgebraicGeometry.AlgebraicSpace.residueFieldTrdegAt.eq_zero_of_mem_finiteTypePoints :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFiniteType f] [IsJacobson Y] {x : Points X},
      x ∈ finiteTypePoints X → residueFieldTrdegAt f x = 0)
