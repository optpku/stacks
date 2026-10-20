/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.Sheaves.LocallyConstant
public import ReasLib.Topology.Specialization.Dimension.Catenary

/-!
# Cohomological Obstruction to Dimension Functions

This optional, sheaf-cohomology-dependent leaf constructs the obstruction class for gluing local
dimension functions (Stacks, Remark 02ID). It is deliberately not imported by the lightweight
dimension aggregate.

Let `ℤ_X = locallyConstantSheaf X ℤ` be the constant sheaf in the sense of Stacks (locally
constant functions). Over an open `U`, the sheaf `dimensionFunctionExtensionSheaf X` has sections
the pairs `(f, n)` of a function `f : U → ℤ` and a locally constant `n : U → ℤ` such that
`f - n • δ` is locally constant for every dimension function `δ` on an open `V ⊆ U`. Locally
`f = n • δ + c`; the sheaf is the extension of `ℤ_X` by `ℤ_X` obtained from the `ℤ_X`-torsor of
local dimension functions. On a catenary locally Noetherian sober space it is short exact
(Lemmas 02IB and 02IC), and its `Ext¹` class is the obstruction
`TopologicalSpace.CatenarySpace.dimensionFunctionObstruction ∈ H¹(X, ℤ_X)`, which vanishes exactly
when a global dimension function exists.

## Main declarations

- `TopologicalSpace.dimensionFunctionExtensionSheaf`: the extension sheaf of local dimension
  functions
- `TopologicalSpace.dimensionFunctionExtension`: the short complex `ℤ_X ⟶ E ⟶ ℤ_X`
- `TopologicalSpace.CatenarySpace.dimensionFunctionObstruction`: its class in `H¹(X, ℤ_X)`
- `TopologicalSpace.CatenarySpace.dimensionFunctionObstruction_eq_zero_iff`: vanishing criterion
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe w u

namespace TopologicalSpace

variable (X : Type u) [TopologicalSpace X]

/-- Sections over `U` of the extension sheaf of local dimension functions: pairs `(f, n)` with
`n` locally constant such that `f - n • δ` is locally constant on every open `V ⊆ U` carrying a
dimension function `δ`. -/
def dimensionFunctionExtensionSubgroup (U : Opens X) :
    AddSubgroup ((U → ℤ) × LocallyConstant U ℤ) where
  carrier := {p | ∀ (V : Opens X) (hVU : V ≤ U) (δ : V → ℤ), IsDimensionFunction δ →
    IsLocallyConstant fun y : V ↦ p.1 (Set.inclusion hVU y) - p.2 (Set.inclusion hVU y) * δ y}
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

variable {X} in
/-- Membership in `dimensionFunctionExtensionSubgroup`. -/
theorem mem_dimensionFunctionExtensionSubgroup {U : Opens X}
    (p : (U → ℤ) × LocallyConstant U ℤ) :
    p ∈ dimensionFunctionExtensionSubgroup X U ↔
      ∀ (V : Opens X) (hVU : V ≤ U) (δ : V → ℤ), IsDimensionFunction δ →
        IsLocallyConstant fun y : V ↦
          p.1 (Set.inclusion hVU y) - p.2 (Set.inclusion hVU y) * δ y :=
  Iff.rfl

/-- Relative to a dimension function on `U`, the extension condition is precisely that
`f - n • δ` is locally constant. Thus the definition does not choose a local dimension function. -/
theorem mem_dimensionFunctionExtensionSubgroup_iff_of_dimensionFunction
    [LocallyNoetherianSpace X] [QuasiSober X]
    (U : Opens X) (δ : U → ℤ) (hδ : IsDimensionFunction δ)
    (p : (U → ℤ) × LocallyConstant U ℤ) :
    p ∈ dimensionFunctionExtensionSubgroup X U ↔
      IsLocallyConstant (fun y : U ↦ p.1 y - p.2 y * δ y) := sorry

/-- The fibre over the constant section `1` is the torsor of dimension functions. -/
theorem mem_dimensionFunctionExtensionSubgroup_one_iff
    [LocallyNoetherianSpace X] [T0Space X] [QuasiSober X] [CatenarySpace X]
    (U : Opens X) (f : U → ℤ) :
    (f, LocallyConstant.const U (1 : ℤ)) ∈ dimensionFunctionExtensionSubgroup X U ↔
      IsDimensionFunction f := sorry

/-- Restriction of sections of the extension sheaf along `V ≤ U`. -/
def dimensionFunctionExtensionRestrict {U V : Opens X} (hVU : V ≤ U) :
    dimensionFunctionExtensionSubgroup X U →+ dimensionFunctionExtensionSubgroup X V where
  toFun p := ⟨(p.1.1 ∘ Set.inclusion hVU, locallyConstantRestrict ℤ hVU p.1.2), sorry⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The presheaf of abelian groups of pairs `(f, n)` that are locally `n • δ + c`. -/
def dimensionFunctionExtensionPresheaf : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (dimensionFunctionExtensionSubgroup X U.unop)
  map i := AddCommGrpCat.ofHom (dimensionFunctionExtensionRestrict X i.unop.le)
  map_id _ := by ext <;> rfl
  map_comp _ _ := by ext <;> rfl

/-- The extension presheaf satisfies the sheaf condition. -/
theorem isSheaf_dimensionFunctionExtensionPresheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (dimensionFunctionExtensionPresheaf X) :=
  sorry

/-- The extension sheaf of local dimension functions. -/
def dimensionFunctionExtensionSheaf : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  ⟨dimensionFunctionExtensionPresheaf X, isSheaf_dimensionFunctionExtensionPresheaf X⟩

/-- The inclusion `c ↦ (c, 0)` of locally constant functions into the extension sheaf. -/
def locallyConstantToDimensionFunctionExtension :
    locallyConstantSheaf X ℤ ⟶ dimensionFunctionExtensionSheaf X :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun c := ⟨((c : U.unop → ℤ), 0), sorry⟩
          map_zero' := rfl
          map_add' _ _ := by ext <;> simp }
      naturality _ _ _ := by ext; rfl }

/-- The projection `(f, n) ↦ n` from the extension sheaf to locally constant functions. -/
def dimensionFunctionExtensionToLocallyConstant :
    dimensionFunctionExtensionSheaf X ⟶ locallyConstantSheaf X ℤ :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun p := p.1.2
          map_zero' := rfl
          map_add' _ _ := rfl }
      naturality _ _ _ := by ext; rfl }

/-- The short complex `ℤ_X ⟶ E ⟶ ℤ_X` of the extension of `ℤ_X` by `ℤ_X` given by local
dimension functions. -/
def dimensionFunctionExtension : ShortComplex (Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}) :=
  ShortComplex.mk (locallyConstantToDimensionFunctionExtension X)
    (dimensionFunctionExtensionToLocallyConstant X) (by ext; rfl)

/-- On a catenary locally Noetherian sober space the extension of local dimension functions is
short exact: its kernel part is Lemma 02IB and its local surjectivity is Lemma 02IC. -/
theorem dimensionFunctionExtension_shortExact
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [LocallyNoetherianSpace X] [T0Space X] [QuasiSober X] [CatenarySpace X] :
    (dimensionFunctionExtension X).ShortExact where
  exact :=
    { condition := ⟨ShortComplex.HomologyData.ofAbelian (dimensionFunctionExtension X),
        (Limits.IsZero.iff_id_eq_zero _).2 (by sorry)⟩ }
  mono_f := sorry
  epi_g := sorry

namespace CatenarySpace

variable [LocallyNoetherianSpace X] [T0Space X] [QuasiSober X] [CatenarySpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- Remark 5.20.5: the obstruction to a global dimension function on a catenary locally
Noetherian sober space, as an element of `H¹(X, ℤ)`. It is the `Ext¹` class of the extension
of local dimension functions, pulled back along the identification of mathlib's constant sheaf
with the sheaf of locally constant integer-valued functions. -/
@[stacks 02ID]
noncomputable def dimensionFunctionObstruction : (locallyConstantSheaf X ℤ).H 1 :=
  (Abelian.Ext.mk₀ (constantSheafToLocallyConstantSheaf X ℤ
      (AddEquiv.ulift : ULift.{u} ℤ ≃+ ℤ).toAddMonoidHom)).comp
    (dimensionFunctionExtension_shortExact X).extClass (zero_add 1)

/-- Remark 5.20.5: the obstruction class vanishes exactly when `X` has a global dimension
function. -/
@[stacks 02ID]
theorem dimensionFunctionObstruction_eq_zero_iff :
    dimensionFunctionObstruction X = 0 ↔ ∃ δ : X → ℤ, IsDimensionFunction δ := sorry

end CatenarySpace

end TopologicalSpace
