module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Pushforward.InternalHom

/-! # Perfect derived pushforward of sheaf Hom -/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived

universe u

/- Lemma 75.22.3: Derived sheaf Hom from a perfect object into a bounded coherent
relatively flat complex with proper support has perfect derived pushforward. -/
@[stacks 0DKK] #check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pushforwardDerived_internalHom_isPerfect :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
    (E : ModuleDerived X) (hE : IsPerfect E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
    (hG_flat : ∀ i : ℤ, Modules.flatOver (G.X i) f)
    (hG_support : ∀ i : ℤ, Proper ((ClosedSubspaceStructure.reduced
      (Closeds.closure (Modules.moduleSupport (G.X i)))).ι ≫ f)),
    IsPerfect ((Modules.moduleDerivedPushforward f).obj
      (InternalHom.obj E (DerivedCategory.Q.obj G))))

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pushforwardDerived_internalHom_single_isPerfect :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
    (E : ModuleDerived X) (hE : IsPerfect E) (G : Modules X)
    (hG_coherent : G.IsCoherent) (hG_flat : Modules.flatOver G f)
    (hG_support : Proper ((ClosedSubspaceStructure.reduced
      (Closeds.closure (Modules.moduleSupport G))).ι ≫ f)),
    IsPerfect ((Modules.moduleDerivedPushforward f).obj
      (InternalHom.obj E ((DerivedCategory.singleFunctor (Modules X) 0).obj G))))

