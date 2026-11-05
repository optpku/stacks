/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Completion
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.TorsionComplete
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local cohomology and canonical derived Hom

For a finitely generated ideal, this file compares canonical derived Hom between derived
completions with canonical derived Hom between the corresponding local-cohomology objects.
-/

@[expose] public section

open CategoryTheory
open DerivedCategory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology

open Completion InternalHom

variable {A : Type u} [CommRing A]

/-- The canonical comparison from derived Hom between completions to derived Hom between the
corresponding closed-support local-cohomology objects. -/
noncomputable def rHomComparison
    (I : Ideal A) (hI : I.FG)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ)
    (K L : DerivedCategory (ModuleCat A)) :
    RHom.obj (derivedCompletionOf I hI K) (derivedCompletionOf I hI L) ⟶
      RHom.obj (RΓZ.obj K).obj (RΓZ.obj L).obj :=
  RHom.map (derivedCompletionCounit I hI RΓZ hRΓZ K)
      (inv (derivedCompletionCounit I hI RΓZ hRΓZ L)) ≫
    RHom.map (toDerivedCompletion I hI (RΓZ.obj K).obj)
      (𝟙 (derivedCompletionOf I hI (RΓZ.obj L).obj)) ≫
    inv (RHom.map (𝟙 (RΓZ.obj K).obj)
      (toDerivedCompletion I hI (RΓZ.obj L).obj))

/-- The local-cohomology derived-Hom comparison is the composite of the completion-counit maps,
the source completion unit, and the inverse target completion map. -/
theorem rHomComparison_def
    (I : Ideal A) (hI : I.FG)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ)
    (K L : DerivedCategory (ModuleCat A)) :
    rHomComparison I hI RΓZ hRΓZ K L =
      RHom.map (derivedCompletionCounit I hI RΓZ hRΓZ K)
          (inv (derivedCompletionCounit I hI RΓZ hRΓZ L)) ≫
        RHom.map (toDerivedCompletion I hI (RΓZ.obj K).obj)
          (𝟙 (derivedCompletionOf I hI (RΓZ.obj L).obj)) ≫
        inv (RHom.map (𝟙 (RΓZ.obj K).obj)
          (toDerivedCompletion I hI (RΓZ.obj L).obj)) := rfl

/-- The canonical comparison from derived Hom between derived completions to derived Hom between
the corresponding closed-support local-cohomology objects is an isomorphism. -/
@[stacks 0A6Y, instance]
noncomputable instance rHomComparisonIsIso
    (I : Ideal A) (hI : I.FG)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ)
    (X Y : DerivedCategory (ModuleCat A)) :
    IsIso (rHomComparison I hI RΓZ hRΓZ X Y) := sorry

end CategoryTheory.DerivedCategory.LocalCohomology
