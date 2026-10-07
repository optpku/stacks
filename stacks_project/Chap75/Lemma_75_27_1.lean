module

public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Lemma_66_18_6_Site
public import stacks_project.Chap66.Lemma_66_31_3_LocallyProjective
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_3_1_Restrict
public import stacks_project.Chap75.Lemma_75_5_6_Instances
public import stacks_project.Chap75.Lemma_75_10_5_Gamma

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory
open CategoryTheory.DerivedCategory
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Lemma 75.27.1 (1): if `X` is a quasi-compact and quasi-separated algebraic space over a
scheme `S` and `K` is an object of `D_QCoh(𝒪_X)` whose cohomology sheaves have countable
sections on affine schemes étale over `X`, then for every quasi-compact and quasi-separated
étale morphism `f : U ⟶ X` and every perfect object `E` of `D(𝒪_X)`, the hypercohomology
groups `H^i(U, K ⊗ᴸ E)` are countable. -/
@[stacks 0CRU]
theorem tensorEtaleHypercohomologyCountable {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (K : DerivedQCoh X)
    (hK : ∀ (j : ℤ) (U : affineEtaleSite X),
      Countable
        (sectionModule ((DerivedCategory.homologyFunctor (Modules X) j).obj K.obj) U.obj))
    {U : AlgebraicSpace S} (f : U ⟶ X) [Etale f] [QuasiCompact f] [QuasiSeparated f]
    (E : ModuleDerived X) (hE : ModuleDerived.IsPerfect E) (i : ℤ) :
    Countable
      (cohomologyAb U
        ((restrictFunctorDerived f).obj ((DerivedTensor.Right.functor E).obj K.obj)) i) :=
  sorry

/-- Lemma 75.27.1 (2): under the same hypotheses, the groups `Ext⁽i⁾(E|_U, K|_U)` are
countable. -/
@[stacks 0CRU]
theorem restrictedExtCountable {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (K : DerivedQCoh X)
    (hK : ∀ (j : ℤ) (U : affineEtaleSite X),
      Countable
        (sectionModule ((DerivedCategory.homologyFunctor (Modules X) j).obj K.obj) U.obj))
    {U : AlgebraicSpace S} (f : U ⟶ X) [Etale f] [QuasiCompact f] [QuasiSeparated f]
    (E : ModuleDerived X) (hE : ModuleDerived.IsPerfect E) (i : ℤ) :
    Countable
      (Ext⁽i⁾((restrictFunctorDerived f).obj E,
        (restrictFunctorDerived f).obj K.obj)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
