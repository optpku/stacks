/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.FormalCompletion.Boundedness

/-!
# Pseudo-coherence of formal-completion homotopy limits

The quasi-coherent coreflection of an ambient homotopy limit of the
pushforwards of a compatible pseudo-coherent formal-completion system is
pseudo-coherent on the ambient algebraic space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System

section

variable {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
variable {X : AlgebraicSpace (Spec A_lim.cone.pt)}
variable {Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)}
variable {p : ∀ n, Xn n ⟶ X}
variable {q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n}
variable {i : ∀ n, Xn n ⟶ Xn (n + 1)}
variable [Proper (SchemeRealization.toBase X)] [Flat (SchemeRealization.toBase X)]
variable [FinitePresentation (SchemeRealization.toBase X)]

/-- The quasi-coherent coreflection of an ambient homotopy limit of the
pushforwards of a formal-completion system is pseudo-coherent on the
ambient algebraic space. -/
theorem coheratorHomotopyLimit_isPseudoCoherent (S : System A A_lim X Xn p q i)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.moduleDerivedPushforward (p n)).obj (S.K n))
    (stageIso_naturality : ∀ n,
      Ksys.stepMap n ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ S.pushforwardTransition n)
    (Klim : ModuleDerived X) (hKlim : HomotopyLimit.IsOf Ksys Klim) :
    IsPseudoCoherent X ((DerivedQCoh.inclusion X).rightAdjoint.obj Klim).obj :=
  sorry

end

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System
