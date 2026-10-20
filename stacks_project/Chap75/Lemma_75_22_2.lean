module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Pushforward.Tensor
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open CategoryTheory.DerivedCategory TopologicalSpace

universe u

/- Lemma 75.22.2: let `S` be a scheme and let `B` be a Noetherian algebraic space
over `S`. Let `f : X ⟶ B` be a morphism of algebraic spaces which is locally of
finite type and quasi-separated. If `E` is a perfect object of `D(𝒪_X)` and `G`
is a bounded complex of coherent `𝒪_X`-modules that are flat over `B` with
support proper over `B`, then
`K = (Modules.moduleDerivedPushforward f).obj (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))`
is a perfect object of `D(𝒪_B)`. -/
@[stacks 0DKJ] #check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pushforwardDerived_tensor_isPerfect :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
    (E : ModuleDerived X) (hE : IsPerfect E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
    (hG_flat : ∀ i : ℤ, Modules.flatOver (G.X i) f)
    (hG_support : ∀ i : ℤ, ClosedSubset.ProperOver f
      (Closeds.closure (Modules.moduleSupport (G.X i)))),
    IsPerfect ((Modules.moduleDerivedPushforward f).obj
      (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))))

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pushforwardDerived_tensor_single_isPerfect :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
    (E : ModuleDerived X) (hE : IsPerfect E) (G : Modules X)
    (hG_coherent : G.IsCoherent) (hG_flat : Modules.flatOver G f)
    (hG_support : ClosedSubset.ProperOver f
      (Closeds.closure (Modules.moduleSupport G))),
    IsPerfect ((Modules.moduleDerivedPushforward f).obj
      (DerivedTensor.Right.obj E ((DerivedCategory.singleFunctor (Modules X) 0).obj G))))
