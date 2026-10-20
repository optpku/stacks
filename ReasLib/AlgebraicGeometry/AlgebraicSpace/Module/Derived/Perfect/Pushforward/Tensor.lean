module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubset.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.Algebra.Homology.CochainComplex.Bounded

/-!
# Perfect derived tensor pushforwards on algebraic spaces

The derived tensor of a perfect object with a bounded relatively flat coherent
complex with proper support has perfect derived pushforward to a Noetherian
algebraic space.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Along a locally of finite type quasi-separated morphism to a Noetherian
algebraic space, the derived pushforward of the derived tensor of a perfect
object with a bounded complex of coherent modules that are flat over the target
and have proper support over the target is perfect. -/
theorem pushforwardDerived_tensor_isPerfect
    (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
    (E : ModuleDerived X) (hE : IsPerfect E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
    (hG_flat : ∀ i : ℤ, Modules.flatOver (G.X i) f)
    (hG_support : ∀ i : ℤ, ClosedSubset.ProperOver f
      (Closeds.closure (Modules.moduleSupport (G.X i)))) :
    IsPerfect ((Modules.moduleDerivedPushforward f).obj
      (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))) := sorry

/-- Derived pushforward of the derived tensor of a perfect object with a single
coherent `𝒪_X`-module that is flat over `B` with support proper over `B` is
perfect. -/
theorem pushforwardDerived_tensor_single_isPerfect
    (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
    (E : ModuleDerived X) (hE : IsPerfect E) (G : Modules X)
    (hG_coherent : G.IsCoherent) (hG_flat : Modules.flatOver G f)
    (hG_support : ClosedSubset.ProperOver f
      (Closeds.closure (Modules.moduleSupport G))) :
    IsPerfect ((Modules.moduleDerivedPushforward f).obj
      (DerivedTensor.Right.obj E ((DerivedCategory.singleFunctor (Modules X) 0).obj G))) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
