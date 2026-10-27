/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.FormalCompletion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RightAdjoint.Exact
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Preservation

/-!
# Boundedness of formal-completion homotopy limits

The quasi-coherent coreflection of a homotopy limit of the derived pushforwards
of a compatible pseudo-coherent formal-completion system is bounded above.
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
variable [Proper (SchemeRealization.toBase X)] [Flat (SchemeRealization.toBase X)] [FinitePresentation (SchemeRealization.toBase X)]

/-- The successor map of the inverse system of derived pushforwards of the
stage complexes, obtained by adjoining the derived-pullback transition,
composing the iterated pushforward, and transporting along `S.comp_p`. -/
def pushforwardTransition (S : System A A_lim X Xn p q i) (n : ℕ) :
    (Modules.moduleDerivedPushforward (p (n + 1))).obj (S.K (n + 1)) ⟶
      (Modules.moduleDerivedPushforward (p n)).obj (S.K n) :=
  (Modules.moduleDerivedPushforward (p (n + 1))).map
      (((Modules.derivedPullbackPushforwardAdjunction (i n)).homEquiv
          (S.K (n + 1)) (S.K n)) (S.transitionIso n).hom) ≫
    (Modules.pushforwardDerived.compIso (i n) (p (n + 1))).hom.app (S.K n) ≫
    eqToHom (congrArg (fun g : Xn n ⟶ X ↦
      (Modules.moduleDerivedPushforward g).obj (S.K n)) (S.comp_p n))

/-- `pushforwardTransition` is the adjoint of the derived-pullback transition,
followed by the derived-pushforward composition isomorphism and the
identification `i n ≫ p (n + 1) = p n`. -/
theorem pushforwardTransition_spec (S : System A A_lim X Xn p q i) (n : ℕ) :
    S.pushforwardTransition n =
      (Modules.moduleDerivedPushforward (p (n + 1))).map
          (((Modules.derivedPullbackPushforwardAdjunction (i n)).homEquiv
              (S.K (n + 1)) (S.K n)) (S.transitionIso n).hom) ≫
        (Modules.pushforwardDerived.compIso (i n) (p (n + 1))).hom.app (S.K n) ≫
        eqToHom (congrArg (fun g : Xn n ⟶ X ↦
          (Modules.moduleDerivedPushforward g).obj (S.K n)) (S.comp_p n)) :=
  rfl

/-- The quasi-coherent coreflection of an ambient homotopy limit of the
pushforwards of a formal-completion system is bounded above. -/
theorem coheratorHomotopyLimit_isBoundedAbove (S : System A A_lim X Xn p q i)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.moduleDerivedPushforward (p n)).obj (S.K n))
    (stageIso_naturality : ∀ n,
      Ksys.stepMap n ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ S.pushforwardTransition n)
    (Klim : ModuleDerived X) (hKlim : HomotopyLimit.IsOf Ksys Klim) :
    DerivedCategory.IsBoundedAbove
      ((DerivedQCoh.inclusion X).rightAdjoint.obj Klim).obj :=
  sorry

end

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System
