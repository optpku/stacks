/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import stacks_project.Chap90.Lemma_90_12_6_Derivation
public import stacks_project.Chap90.Lemma_90_12_2_Tensor
public import stacks_project.Chap90.Remarks_90_5_2_IsoClass

/-!
# Derivation action on square-zero fibre isomorphism classes

A derivation `D : Derivation Λ k V` determines maps `γ_V` and `a_V` on the fibrewise
isomorphism-class functor of a predeformation category, by pushforward along
`f_D` and `f_{1,D}` respectively.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat Functor

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k)

noncomputable section

namespace CategoryTheory.Functor

variable [IsPredeformationCategory p]
variable (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V]
  [Module Λ V] [IsScalarTower Λ k V]

/-- The map `γ_V` sending a derivation `D` to the isomorphism class `f_{D,*}(x_0)` in
`F-bar(k[V])`, independent of the residue-fibre object `x_0`. -/
def isoClassOfDerivation (D : Derivation Λ k V) :
    (fiberIsoClassFunctor p).obj (squareZero Λ k V) :=
  (fiberIsoClassFunctor p).map (derivationToSquareZero D) default

/-- `isoClassOfDerivation p V D` is the isomorphism class of the pushforward of any
residue-fibre object along `derivationToSquareZero D`. -/
theorem isoClassOfDerivation_apply (x0 : p.Fiber (residue Λ k)) (D : Derivation Λ k V) :
    isoClassOfDerivation p V D =
      Quotient.mk'' (pushforwardFiberObj p (cleavageOp p) (derivationToSquareZero D) x0) :=
  sorry

/-- The action `a_V` of a derivation `D` on `F-bar(k[V])`, given by pushforward along
`squareZeroAut D`. -/
def squareZeroDerivationAction (D : Derivation Λ k V)
    (x : (fiberIsoClassFunctor p).obj (squareZero Λ k V)) :
    (fiberIsoClassFunctor p).obj (squareZero Λ k V) :=
  (fiberIsoClassFunctor p).map (squareZeroAut D) x

/-- On a represented class, the action is the isomorphism class of the chosen pushforward
of the fibre representative. -/
theorem squareZeroDerivationAction_mk (D : Derivation Λ k V)
    (x : p.Fiber (squareZero Λ k V)) :
    squareZeroDerivationAction p V D (Quotient.mk'' x) =
      Quotient.mk'' (pushforwardFiberObj p (cleavageOp p) (squareZeroAut D) x) :=
  sorry

variable [HasSchlessingerH2 (fiberIsoClassFunctor p)]

/-- The map `γ_V` as a bundled `k`-linear map, when `F-bar` satisfies (S2). -/
def isoClassOfDerivationLinear :
    Derivation Λ k V →ₗ[k] (fiberIsoClassFunctor p).obj (squareZero Λ k V) where
  toFun := isoClassOfDerivation p V
  map_add' := sorry
  map_smul' := sorry

/-- The underlying function of `isoClassOfDerivationLinear` is `isoClassOfDerivation`. -/
theorem isoClassOfDerivationLinear_apply (D : Derivation Λ k V) :
    isoClassOfDerivationLinear p V D = isoClassOfDerivation p V D := sorry

end CategoryTheory.Functor

end
