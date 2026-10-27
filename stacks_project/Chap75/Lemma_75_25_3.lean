/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.TensorPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.TensorPushforward

/-!
# Pseudo-coherent tensor pushforward and arbitrary base change

Along a finite-presentation morphism of algebraic spaces, the derived pushforward of a
pseudo-coherent object tensored with a bounded-above, degreewise finitely presented,
relatively flat complex with degreewise proper support is pseudo-coherent. Its formation
commutes with arbitrary base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open CategoryTheory.DerivedCategory TopologicalSpace

universe u

/- Lemma 75.25.3: the tensor pushforward is pseudo-coherent under the finite-presentation,
relative-flatness, boundedness-above, and degreewise proper-support hypotheses. -/
@[stacks 0CTL] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pushforwardDerived_tensor_isPseudoCoherent_of_finitePresentation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FinitePresentation f] (E : ModuleDerived X)
    (hE : IsPseudoCoherent X E) (G : CochainComplex (Modules X) ℤ)
    (hG_minus : CochainComplex.minus (Modules X) G)
    (hG_fp : ∀ i : ℤ, (G.X i).IsFinitePresentation)
    (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x)
    (hG_support : ∀ i : ℤ, ClosedSubset.ProperOver f
      (Closeds.closure (Modules.moduleSupport (G.X i)))),
    IsPseudoCoherent Y ((Modules.moduleDerivedPushforward f).obj
      (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))))

/- Finite presentation gives quasi-compactness and quasi-separatedness of the morphism.
Pseudo-coherence gives quasi-coherent cohomology, and degreewise finite presentation gives
degreewise quasi-coherence. Thus the following general theorem supplies the arbitrary
base-change assertion under the hypotheses above, with derived pullback of E and ordinary
termwise pullback of G. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforwardTensorBaseChange_isIso :
    ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (sq : IsPullback g' f' f g)
    (E : DerivedQCoh X) (G : CochainComplex (Modules X) ℤ)
    (hG_minus : CochainComplex.minus (Modules X) G)
    (hG_qcoh : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (hG_flat : ∀ n : ℤ, ∀ x, Modules.flatOverAt (G.X n) f x),
    IsIso (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.tensorPushforwardBaseChange
      g' f' f g sq E G))
