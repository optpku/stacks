/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Pushforward.InternalHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.InternalHomPushforward

/-!
# Perfect derived pushforward of internal Hom into a bounded relatively flat finitely presented complex

Along a morphism of finite presentation of algebraic spaces, the derived pushforward of the
derived internal Hom from a perfect object into a bounded complex of finitely presented modules
that are flat over the target with support proper over the target is perfect, and its formation
commutes with arbitrary base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}

/- Lemma 75.25.8: derived pushforward of canonical derived sheaf Hom from a perfect
object to a bounded, degreewise finitely presented, relatively flat complex with proper
support is perfect, and its formation commutes with arbitrary base change. -/
@[stacks 0A1R] #check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pushforwardDerived_internalHom_isPerfect_of_finitePresentation :
  ∀ (f : X ⟶ Y) [FinitePresentation f]
    (E : ModuleDerived X) (hE : IsPerfect E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_fp : ∀ i : ℤ, (G.X i).IsFinitePresentation)
    (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x)
    (hG_support : ∀ i : ℤ, Proper ((ClosedSubspaceStructure.reduced
      (Closeds.closure (Modules.moduleSupport (G.X i)))).ι ≫ f)),
    IsPerfect ((Modules.moduleDerivedPushforward f).obj
      (InternalHom.obj E (DerivedCategory.Q.obj G))))

/- FinitePresentation supplies quasi-compactness and quasi-separatedness, boundedness
supplies bounded-aboveness, and degreewise finite presentation supplies quasi-coherence.
Thus the canonical comparison below gives arbitrary base change under the hypotheses
above, using ordinary termwise pullback of the coefficient complex. -/
#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforwardInternalHomBaseChange_isIso_of_isPerfect :
  ∀ (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (sq : IsPullback g' f' f g) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (hE : IsPerfect E)
    (hG_minus : CochainComplex.minus (Modules X) G)
    (hG_qcoh : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (hG_flat : ∀ n : ℤ, ∀ x, Modules.flatOverAt (G.X n) f x),
    IsIso (DerivedQCoh.internalHomPushforwardBaseChange g' f' f g sq E G))

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
