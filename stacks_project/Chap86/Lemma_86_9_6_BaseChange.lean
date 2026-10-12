/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap86.Definition_86_9_1_RelativeDualizing

/-!
# Base change of relative dualizing complexes of algebraic spaces

Cartesian base change of a relative dualizing complex along a square of algebraic
spaces yields the pulled pair `(L(g')^* ω, Lg^* τ)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex

/-- Cartesian base change of a relative dualizing complex: if `(ω, τ)` is a relative
dualizing complex for `f`, then `(L(g')^* ω, Lg^* τ)` is a relative dualizing complex
for `f'`. -/
noncomputable def baseChange {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    [Proper f'] [Flat f'] [FinitePresentation f']
    (sq : IsPullback g' f' f g) (C : RelativeDualizingComplex f)
    (adj_f : ModuleDerived.pullback f ⊣ moduleDerivedPushforward f)
    (adj_f' : ModuleDerived.pullback f' ⊣ moduleDerivedPushforward f')
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    [IsIso (baseChangeMate g' f' f g sq adj_f adj_f' C.complex)] :
    RelativeDualizingComplex f' :=
  of f' ((ModuleDerived.pullback g').obj C.complex)
    (baseChangedTrace g' f' f g sq adj_f adj_f' C.trace) sorry sorry

/-- The complex of the base-changed pair is `L(g')^* ω`. -/
theorem baseChange_complex {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    [Proper f'] [Flat f'] [FinitePresentation f']
    (sq : IsPullback g' f' f g) (C : RelativeDualizingComplex f)
    (adj_f : ModuleDerived.pullback f ⊣ moduleDerivedPushforward f)
    (adj_f' : ModuleDerived.pullback f' ⊣ moduleDerivedPushforward f')
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    [IsIso (baseChangeMate g' f' f g sq adj_f adj_f' C.complex)] :
    (baseChange g' f' f g sq C adj_f adj_f').complex =
      (ModuleDerived.pullback g').obj C.complex :=
  sorry

/-- The trace of the base-changed pair is `Lg^* τ`. -/
theorem baseChange_trace {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    [Proper f'] [Flat f'] [FinitePresentation f']
    (sq : IsPullback g' f' f g) (C : RelativeDualizingComplex f)
    (adj_f : ModuleDerived.pullback f ⊣ moduleDerivedPushforward f)
    (adj_f' : ModuleDerived.pullback f' ⊣ moduleDerivedPushforward f')
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    [IsIso (baseChangeMate g' f' f g sq adj_f adj_f' C.complex)] :
    (baseChange g' f' f g sq C adj_f adj_f').trace =
      baseChangedTrace g' f' f g sq adj_f adj_f' C.trace :=
  sorry

/-- The base-changed pair is `Y'`-perfect and satisfies affine cartesian base change. -/
theorem baseChange_spec {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    [Proper f'] [Flat f'] [FinitePresentation f']
    (sq : IsPullback g' f' f g) (C : RelativeDualizingComplex f)
    (adj_f : ModuleDerived.pullback f ⊣ moduleDerivedPushforward f)
    (adj_f' : ModuleDerived.pullback f' ⊣ moduleDerivedPushforward f')
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)]
    [IsIso (baseChangeMate g' f' f g sq adj_f adj_f' C.complex)] :
    IsPerfectRelativeTo f' (baseChange g' f' f g sq C adj_f adj_f').complex ∧
      affineBaseChangeCondition f' (baseChange g' f' f g sq C adj_f adj_f').complex
        (baseChange g' f' f g sq C adj_f adj_f').trace :=
  sorry

/-- The derived base-change mate of a cartesian square is an isomorphism on a relative
dualizing complex. -/
theorem baseChangeMate_isIso {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    (sq : IsPullback g' f' f g) (C : RelativeDualizingComplex f)
    (adj_f : ModuleDerived.pullback f ⊣ moduleDerivedPushforward f)
    (adj_f' : ModuleDerived.pullback f' ⊣ moduleDerivedPushforward f')
    [IsIso (ModuleDerived.pullbackCompComparison f' g)]
    [IsIso (ModuleDerived.pullbackCompComparison g' f)] :
    IsIso (baseChangeMate g' f' f g sq adj_f adj_f' C.complex) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex
