/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.FormalCompletion.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
import Mathlib.Tactic.CrossRefAttribute

/-! # Cohomology of formal completions against perfect complexes -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open FormalCompletion FormalCompletion.System
open CategoryTheory.DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System

variable {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
variable {X : AlgebraicSpace (Spec A_lim.cone.pt)}
variable {Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)}
variable {p : ∀ n, Xn n ⟶ X}
variable {q : ∀ n, Xn n ⟶ Modules.stageSpec A_lim n}
variable {i : ∀ n, Xn n ⟶ Xn (n + 1)}
variable [Proper (SchemeRealization.toBase X)] [Flat (SchemeRealization.toBase X)] [FinitePresentation (SchemeRealization.toBase X)]

/-- Tensoring the quasi-coherent coreflection of a compatible formal-completion homotopy
limit with a perfect complex has pseudo-coherent global sections over the limit ring. -/
@[stacks 0DIM]
theorem globalSectionsTensor_isPseudoCoherent
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.moduleDerivedPushforward (p n)).obj (S.K n))
    (stageIso_naturality : ∀ n,
      Ksys.stepMap n ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ S.pushforwardTransition n)
    (Klim : ModuleDerived X) (hKlim : HomotopyLimit.IsOf Ksys Klim)
    (E : ModuleDerived X) (hE : ModuleDerived.IsPerfect E) :
    DerivedCategory.IsPseudoCoherent
      (globalSectionsTensor Klim E) :=
  sorry

/-- Derived global sections of the tensor with a perfect complex recover the finite-stage
global sections by the canonical derived scalar-extension comparison. -/
@[stacks 0DIM]
theorem globalSectionsTensorBaseChangeMap_isIso
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (S : System A A_lim X Xn p q i)
    (Ksys : SequentialInverseSystem (ModuleDerived X))
    (stageIso : ∀ n, Ksys.obj (Opposite.op n) ≅
      (Modules.moduleDerivedPushforward (p n)).obj (S.K n))
    (stageIso_naturality : ∀ n,
      Ksys.stepMap n ≫ (stageIso n).hom =
        (stageIso (n + 1)).hom ≫ S.pushforwardTransition n)
    (Klim : ModuleDerived X) (P : HomotopyLimit.Presentation Ksys Klim)
    (E : ModuleDerived X) (hE : ModuleDerived.IsPerfect E) (n : ℕ)
    (Ext : ModuleCat.DerivedExtension (A_lim.cone.stageMap n).hom) :
    IsIso (globalSectionsTensorBaseChangeMap S Ksys stageIso Klim P E n Ext) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.FormalCompletion.System
