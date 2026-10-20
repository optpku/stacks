module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Countability
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory
open CategoryTheory.DerivedCategory
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/- Lemma 75.27.1 (1): if `X` is a quasi-compact and quasi-separated algebraic space over a
scheme `S` and `K` is an object of `D_QCoh(𝒪_X)` whose cohomology sheaves have countable
sections on affine schemes étale over `X`, then for every quasi-compact and quasi-separated
étale morphism `f : U ⟶ X` and every perfect object `E` of `D(𝒪_X)`, the hypercohomology
groups `H^i(U, K ⊗ᴸ E)` are countable. -/
@[stacks 0CRU] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.tensorEtaleHypercohomologyCountable :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (K : DerivedQCoh X)
    (hK : ∀ (j : ℤ) (U : affineEtaleSite X),
      Countable
        (sectionModule ((DerivedCategory.homologyFunctor (Modules X) j).obj K.obj) U.obj))
    {U : AlgebraicSpace S} (f : U ⟶ X) [Etale f] [QuasiCompact f] [QuasiSeparated f]
    (E : ModuleDerived X) (hE : ModuleDerived.IsPerfect E) (i : ℤ),
    Countable
      (cohomologyAb U
        ((restrictFunctorDerived f).obj ((DerivedTensor.Right.functor E).obj K.obj)) i))

/- Lemma 75.27.1 (2), Stacks tag 0CRU: under the same hypotheses, the groups
`Ext⁽i⁾(E|_U, K|_U)` are countable. -/
@[stacks 0CRU] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.restrictedExtCountable :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (K : DerivedQCoh X)
    (hK : ∀ (j : ℤ) (U : affineEtaleSite X),
      Countable
        (sectionModule ((DerivedCategory.homologyFunctor (Modules X) j).obj K.obj) U.obj))
    {U : AlgebraicSpace S} (f : U ⟶ X) [Etale f] [QuasiCompact f] [QuasiSeparated f]
    (E : ModuleDerived X) (hE : ModuleDerived.IsPerfect E) (i : ℤ),
    Countable
      (Ext⁽i⁾((restrictFunctorDerived f).obj E,
        (restrictFunctorDerived f).obj K.obj)))

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
