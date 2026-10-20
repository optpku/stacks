/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.LocalModel

@[expose] public section

/-!
# Open-cover criteria for perfect derived modules

This leaf expresses perfectness through canonical restriction functors and strictly perfect local
models.  The cover constructors accept arbitrary index universes; witness extractors return the
canonical universe of the space.
-/

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

namespace CochainComplex

namespace Perfect

/-- `ModelOn E U` means that the restriction of `E` to `U` admits a strictly perfect
quasi-isomorphic model. -/
abbrev ModelOn
    (E : _root_.CochainComplex (Modules X) ℤ) (U : Opens X.carrier) : Prop :=
  _root_.AlgebraicGeometry.RingedSpace.CochainComplex.HasStrictlyPerfectModel
    ((moduleRestrictionComplexToOpen X U).obj E)

/-- The explicit strictly perfect quasi-isomorphic model described by `ModelOn E U`. -/
theorem modelOn_iff
    (E : _root_.CochainComplex (Modules X) ℤ) (U : Opens X.carrier) :
    ModelOn E U ↔
      ∃ P : _root_.CochainComplex (Modules (X.restrict U.isOpenEmbedding)) ℤ,
        ∃ α : P ⟶ (moduleRestrictionComplexToOpen X U).obj E,
          SheafOfModules.CochainComplex.IsStrictlyPerfect P ∧ QuasiIso α := sorry

end Perfect

/-- A complex of `𝒪_X`-modules is perfect exactly when it has strictly perfect models on
the members of an open cover. -/
theorem isPerfect_iff_exists_openCover
    (E : _root_.CochainComplex (Modules X) ℤ) :
    IsPerfect E ↔
      ∃ (I : Type u) (U : I → Opens X.carrier), IsOpenCover U ∧
        ∀ i : I, Perfect.ModelOn E (U i) := sorry

/-- Strictly perfect models on an open cover exhibit a perfect complex. -/
theorem isPerfect_of_isOpenCover
    {I : Type v} {U : I → Opens X.carrier}
    {E : _root_.CochainComplex (Modules X) ℤ}
    (hU : IsOpenCover U) (hE : ∀ i : I, Perfect.ModelOn E (U i)) :
    IsPerfect E := sorry

/-- A perfect complex admits strictly perfect models on a canonical-universe open cover. -/
theorem IsPerfect.exists_openCover
    {E : _root_.CochainComplex (Modules X) ℤ} (hE : IsPerfect E) :
    ∃ (I : Type u) (U : I → Opens X.carrier), IsOpenCover U ∧
      ∀ i : I, Perfect.ModelOn E (U i) := sorry

end CochainComplex

namespace ModuleDerived

namespace Perfect

/-- `ModelOn K U` is the generic local-model property specialized to strictly perfect
complexes. -/
abbrev ModelOn (K : ModuleDerived X) (U : Opens X.carrier) : Prop :=
  LocalModel.on U
    (fun P : LocalModel.ComplexOn X U ↦
      SheafOfModules.CochainComplex.IsStrictlyPerfect P) K

/-- The explicit strictly perfect representative described by `ModelOn K U`. -/
theorem modelOn_iff (K : ModuleDerived X) (U : Opens X.carrier) :
    ModelOn K U ↔
      ∃ P : _root_.CochainComplex (Modules (X.restrict U.isOpenEmbedding)) ℤ,
        ∃ _ : (moduleRestrictionToOpenDerived X U).obj K ≅ DerivedCategory.Q.obj P,
          SheafOfModules.CochainComplex.IsStrictlyPerfect P := sorry

end Perfect

/-- A derived `𝒪_X`-module is perfect exactly when its restrictions are represented by
strictly perfect complexes on an open cover. -/
theorem isPerfect_iff_exists_openCover (K : ModuleDerived X) :
    IsPerfect K ↔
      ∃ (I : Type u) (U : I → Opens X.carrier), IsOpenCover U ∧
        ∀ i : I, Perfect.ModelOn K (U i) := sorry

/-- Lemma 20.49.2 (1): strictly perfect representatives on an open cover exhibit a perfect
derived `𝒪_X`-module. -/
@[stacks 08CN "(1)"]
theorem isPerfect_of_isOpenCover
    {I : Type v} {U : I → Opens X.carrier} {K : ModuleDerived X}
    (hU : IsOpenCover U) (hK : ∀ i : I, Perfect.ModelOn K (U i)) :
    IsPerfect K := sorry

/-- A perfect derived `𝒪_X`-module admits strictly perfect representatives on a
canonical-universe open cover. -/
theorem IsPerfect.exists_openCover
    {K : ModuleDerived X} (hK : IsPerfect K) :
    ∃ (I : Type u) (U : I → Opens X.carrier), IsOpenCover U ∧
      ∀ i : I, Perfect.ModelOn K (U i) := sorry

end ModuleDerived

end AlgebraicGeometry.RingedSpace
