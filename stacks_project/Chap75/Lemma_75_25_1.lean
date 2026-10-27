/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Pushforward.Tensor.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.TensorPushforward

/-!
# Perfect derived pushforward of a tensor with a bounded relatively flat finitely presented complex

Along a morphism of finite presentation of algebraic spaces, the derived pushforward of the
derived tensor of a perfect object with a bounded complex of finitely presented modules that
are flat over the target with support proper over the target is perfect, and its formation
commutes with arbitrary base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open CategoryTheory.DerivedCategory CategoryTheory.DerivedCategory.DerivedTensor
open TopologicalSpace

noncomputable section

universe u

/- Lemma 75.25.1: the derived pushforward of a perfect object tensored with a bounded,
degreewise finitely presented relatively flat complex with proper support is perfect. -/
@[stacks 0A1P]
#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pushforwardDerived_tensor_isPerfect_of_finitePresentation :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FinitePresentation f] (E : ModuleDerived X)
    (hE : ModuleDerived.IsPerfect E) (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_fp : ∀ i : ℤ, (G.X i).IsFinitePresentation)
    (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x)
    (hG_support : ∀ i : ℤ, ClosedSubset.ProperOver f
      (Closeds.closure (Modules.moduleSupport (G.X i)))),
    ModuleDerived.IsPerfect ((Modules.moduleDerivedPushforward f).obj
      (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))))

/- Perfectness supplies quasi-coherent cohomology of E, so it can be viewed as an object
of DerivedQCoh X without imposing an independent quasi-coherence hypothesis. -/
#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfect.quasiCoherent :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X},
    ModuleDerived.IsPerfect E → derivedQuasiCoherentModuleProperty X E)

/- The arbitrary-base-change conclusion follows from the canonical general theorem below.
Finite presentation of f supplies quasi-compactness and quasi-separatedness. Boundedness
of G supplies bounded-aboveness via CochainComplex.bounded_iff, and finite presentation of
each module supplies quasi-coherence. The preceding implication bundles E as
⟨E, hE.quasiCoherent⟩ : DerivedQCoh X. The canonical comparison uses derived pullback of E
and ordinary termwise pullback of G, for every cartesian square. -/
#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforwardTensorBaseChange_isIso :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (sq : IsPullback g' f' f g)
    (E : DerivedQCoh X) (G : CochainComplex (Modules X) ℤ)
    (hG_minus : CochainComplex.minus (Modules X) G)
    (hG_qcoh : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (hG_flat : ∀ n : ℤ, ∀ x, Modules.flatOverAt (G.X n) f x),
    IsIso (DerivedQCoh.tensorPushforwardBaseChange g' f' f g sq E G))
