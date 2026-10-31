/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.TensorPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubset.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support

/-! # Pseudo-coherent tensor pushforward along finite-presentation morphisms -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Along a finite-presentation morphism of algebraic spaces, the derived pushforward of
a pseudo-coherent object tensored with a bounded-above complex of finitely presented modules
is pseudo-coherent if every term is flat over the target and has support proper over it. -/
theorem pushforwardDerived_tensor_isPseudoCoherent_of_finitePresentation
    (f : X ⟶ Y) [FinitePresentation f] (E : ModuleDerived X)
    (hE : IsPseudoCoherent X E) (G : CochainComplex (Modules X) ℤ)
    (hG_minus : CochainComplex.minus (Modules X) G)
    (hG_fp : ∀ i : ℤ, (G.X i).IsFinitePresentation)
    (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x)
    (hG_support : ∀ i : ℤ, ClosedSubset.ProperOver f
      (Closeds.closure (Modules.moduleSupport (G.X i)))) :
    IsPseudoCoherent Y ((Modules.moduleDerivedPushforward f).obj
      (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
