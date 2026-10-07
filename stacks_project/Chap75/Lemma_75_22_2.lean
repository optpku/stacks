module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
public import stacks_project.Chap67.Lemma_67_31_6_ModuleSupport
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_5_6_Instances
public import stacks_project.Chap75.Lemma_75_7_3_ProperOver

/-!
# Perfect derived pushforward of a tensor with a bounded relatively flat coherent complex

Along a locally of finite type quasi-separated morphism of algebraic spaces with
Noetherian target, the derived pushforward of the derived tensor of a perfect
object with a bounded complex of coherent modules that are flat over the target
with support proper over the target is perfect.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 75.22.2: let `S` be a scheme and let `B` be a Noetherian algebraic space
over `S`. Let `f : X ⟶ B` be a morphism of algebraic spaces which is locally of
finite type and quasi-separated. If `E` is a perfect object of `D(𝒪_X)` and `G`
is a bounded complex of coherent `𝒪_X`-modules that are flat over `B` with
support proper over `B`, then
`K = (Modules.pushforwardDerived f).obj (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))`
is a perfect object of `D(𝒪_B)`. -/
@[stacks 0DKJ]
theorem pushforwardDerived_tensor_isPerfect
    (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
    (E : ModuleDerived X) (hE : IsPerfect E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
    (hG_flat : ∀ i : ℤ, Modules.flatOver (G.X i) f)
    (hG_support : ∀ i : ℤ, ClosedSubset.IsProperOver f
      (Closeds.closure (Modules.moduleSupport (G.X i)))) :
    IsPerfect ((Modules.pushforwardDerived f).obj
      (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))) := sorry

/-- Derived pushforward of the derived tensor of a perfect object with a single
coherent `𝒪_X`-module that is flat over `B` with support proper over `B` is
perfect. -/
theorem pushforwardDerived_tensor_single_isPerfect
    (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
    (E : ModuleDerived X) (hE : IsPerfect E) (G : Modules X)
    (hG_coherent : G.IsCoherent) (hG_flat : Modules.flatOver G f)
    (hG_support : ClosedSubset.IsProperOver f
      (Closeds.closure (Modules.moduleSupport G))) :
    IsPerfect ((Modules.pushforwardDerived f).obj
      (DerivedTensor.Right.obj E ((DerivedCategory.singleFunctor (Modules X) 0).obj G))) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
