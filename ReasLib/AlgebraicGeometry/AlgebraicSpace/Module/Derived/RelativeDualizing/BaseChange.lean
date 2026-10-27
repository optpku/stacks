/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RelativeDualizing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.TorIndependence.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative.BaseChange

/-! # Base change of relative dualizing complexes -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f]
    (sq : IsPullback g' f' f g) (C : RelativeDualizingComplex f)

/-- The native derived base-change map is invertible on a relative dualizing complex
for a proper, flat morphism of finite presentation. -/
theorem baseChangeMap_isIso :
    IsIso (ModuleDerived.baseChangeMap g' f' f g sq C.complex) := sorry

/-- The canonical derived base-change isomorphism on a relative dualizing complex. -/
noncomputable def baseChangeIso :
    (ModuleDerived.pullback g).obj ((moduleDerivedPushforward f).obj C.complex) ≅
      (moduleDerivedPushforward f').obj ((ModuleDerived.pullback g').obj C.complex) :=
  @asIso _ _ _ _ (ModuleDerived.baseChangeMap g' f' f g sq C.complex)
    (baseChangeMap_isIso g' f' f g sq C)

/-- The forward map of the base-change isomorphism is the native derived comparison. -/
theorem baseChangeIso_hom :
    (baseChangeIso g' f' f g sq C).hom =
      ModuleDerived.baseChangeMap g' f' f g sq C.complex := sorry

/-- The base-changed trace is the inverse canonical comparison followed by the
derived pullback of the original trace. -/
noncomputable def baseChangeTrace :
    (moduleDerivedPushforward f').obj ((ModuleDerived.pullback g').obj C.complex) ⟶
      structureSheafDerived Y' :=
  (baseChangeIso g' f' f g sq C).inv ≫ pulledTrace f g C.trace

/-- The native base-change comparison intertwines the base-changed trace and the
derived pullback of the original trace. -/
theorem baseChangeTrace_spec :
    ModuleDerived.baseChangeMap g' f' f g sq C.complex ≫
        baseChangeTrace g' f' f g sq C = pulledTrace f g C.trace := sorry

/-- The derived pullback of a relative dualizing complex is perfect relative to
the base-changed morphism. -/
theorem baseChange_isPerfect :
    @IsPerfectRelativeTo _ _ _ f' (Flat.of_isPullback sq inferInstance)
      (LocallyOfFinitePresentation.of_isPullback sq inferInstance)
      ((ModuleDerived.pullback g').obj C.complex) := sorry

/-- The derived pullback complex and its canonical base-changed trace satisfy
the trace-compatible affine base-change condition. -/
theorem baseChange_affineBaseChange :
    affineBaseChangeCondition f' ((ModuleDerived.pullback g').obj C.complex)
      (baseChangeTrace g' f' f g sq C) := sorry

/-- Cartesian base change carries a relative dualizing complex to the relative
dualizing complex with derived pullback complex and canonical base-changed trace. -/
noncomputable def baseChange :=
  @RelativeDualizingComplex.of _ _ _ f'
    (Proper.of_isPullback sq inferInstance) (Flat.of_isPullback sq inferInstance)
    (FinitePresentation.of_isPullback sq inferInstance)
    ((ModuleDerived.pullback g').obj C.complex) (baseChangeTrace g' f' f g sq C)
    (baseChange_isPerfect g' f' f g sq C) (baseChange_affineBaseChange g' f' f g sq C)

/-- The complex of a base-changed relative dualizing complex is the derived
pullback of the original complex. -/
theorem baseChange_complex :
    let C' := baseChange g' f' f g sq C
    @C'.complex = (ModuleDerived.pullback g').obj C.complex := sorry

/-- The trace of a base-changed relative dualizing complex is the canonical
base-changed trace. -/
theorem baseChange_trace :
    let C' := baseChange g' f' f g sq C
    @C'.trace = baseChangeTrace g' f' f g sq C := sorry

/-- A base-changed relative dualizing complex is relatively perfect and its
trace satisfies the affine base-change condition. -/
theorem baseChange_spec :
    let C' := baseChange g' f' f g sq C
    @IsPerfectRelativeTo _ _ _ f' (Flat.of_isPullback sq inferInstance)
      (LocallyOfFinitePresentation.of_isPullback sq inferInstance)
      @C'.complex ∧ affineBaseChangeCondition f' (@C'.complex) (@C'.trace) := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex
