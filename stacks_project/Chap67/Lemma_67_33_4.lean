module

public import stacks_project.Chap66.Definition_66_7_2
public import stacks_project.Chap66.Remark_66_7_3_EtaleLocal
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_25_4_FiniteTypePoint
public import stacks_project.Chap67.Lemma_67_33_3_ResidueFieldTrdeg

/-!
# Residue-field transcendence degree of finite-type points over Jacobson targets

A locally finite-type morphism of algebraic spaces into an étale-locally
Jacobson target has residue-field transcendence degree 0 at finite-type points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.33.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is locally of finite type, `Y` is Jacobson
in the étale-local sense of Properties of Spaces, Remark 66.7.3
(`hasEtaleLocal` for `JacobsonSpace`), and `x` is a finite-type point of `X`,
then `residueFieldTrdegAt f x = 0`. -/
@[stacks 0ECY]
theorem residueFieldTrdegAt.eq_zero_of_isFiniteTypePoint
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f]
    (h_jacobson : hasEtaleLocal (fun Z : Scheme.{u} ↦ JacobsonSpace Z) Y)
    {x : Points X} (hx : IsFiniteTypePoint x) :
    residueFieldTrdegAt f x = 0 :=
  sorry

/-- The residue-field transcendence degree of a locally finite-type morphism
into an étale-locally Jacobson algebraic space vanishes on `finiteTypePoints`. -/
theorem residueFieldTrdegAt.eq_zero_of_mem_finiteTypePoints
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f]
    (h_jacobson : hasEtaleLocal (fun Z : Scheme.{u} ↦ JacobsonSpace Z) Y)
    {x : Points X} (hx : x ∈ finiteTypePoints X) :
    residueFieldTrdegAt f x = 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
