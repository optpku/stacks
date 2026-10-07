module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Linear
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree.Dualizable
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.CategoryTheory.Monoidal.Closed.Dualizable
public import ReasLib.CategoryTheory.Monoidal.Closed.Exactness

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The dualizing sheaf `omega k d` of `scheme k d` is the twisting sheaf of degree `-d - 1`. -/
abbrev omega (k : Type u) [Field k] (d : ℕ) : (scheme k d).Modules :=
  twistingSheaf k d (-(d : ℤ) - 1)

/-- `omega k d` is the twisting sheaf of degree `-(d : ℤ) - 1`. -/
theorem omega_def (k : Type u) [Field k] (d : ℕ) :
    omega k d = twistingSheaf k d (-(d : ℤ) - 1) := sorry

/-- Finite local freeness on `scheme k d` makes the canonical tensor-to-endomorphism comparison
invertible. -/
instance instIsIso_tensorIhomUnitToEnd {k : Type u} [Field k] {d : ℕ}
    (F : (scheme k d).Modules) [IsFiniteLocallyFree F] :
    IsIso (tensorIhomUnitToEnd F) :=
  IsRightDualizable.isIso_tensorIhomUnitToEnd
    (SheafOfModules.IsFiniteLocallyFree.isRightDualizable
      (F : (scheme k d).toRingedSpace.Modules))

/-- Internal Hom out of a finite locally free module on `scheme k d` preserves finite colimits. -/
instance instPreservesFiniteColimits_ihom {k : Type u} [Field k] {d : ℕ}
    (F : (scheme k d).Modules) [IsFiniteLocallyFree F] :
    PreservesFiniteColimits (ihom F) := sorry

/-- The `k`-linear cup-product pairing
`Ext (E, F ⊗ omega k d) i →ₗ Ext (F, E) (d - i) →ₗ Ext (F, F ⊗ omega k d) d`. -/
def cupProductPairing {k : Type u} [Field k] {d : ℕ} [HasExt (scheme k d).Modules]
    (E F : (scheme k d).Modules) (i : ℕ) (hi : i ≤ d) :
    Ext E (F ⊗ omega k d) i →ₗ[k]
      Ext F E (d - i) →ₗ[k] Ext F (F ⊗ omega k d) d :=
  (Ext.bilinearCompOfLinear k F E (F ⊗ omega k d) (d - i) i d
      (Nat.sub_add_cancel hi)).flip

/-- `cupProductPairing` evaluates as Yoneda composition `β.comp α` in the source argument order. -/
theorem cupProductPairing_apply {k : Type u} [Field k] {d : ℕ} [HasExt (scheme k d).Modules]
    {E F : (scheme k d).Modules} {i : ℕ} (hi : i ≤ d)
    (α : Ext E (F ⊗ omega k d) i) (β : Ext F E (d - i)) :
    cupProductPairing E F i hi α β = β.comp α (Nat.sub_add_cancel hi) := sorry

/-- Sheaf-level generalized trace `(ihom F).obj (F ⊗ G) ⟶ G`, obtained by contracting the
canonical dual of a finite locally free module against evaluation. -/
def sheafTrace {k : Type u} [Field k] {d : ℕ}
    (F G : (scheme k d).Modules) [IsFiniteLocallyFree F] :
    (ihom F).obj (F ⊗ G) ⟶ G :=
  inv (Dual.tensorComparison F (F ⊗ G)) ≫
    (β_ (F ⊗ G) (dual F)).hom ≫ (α_ (dual F) F G).inv ≫ Dual.evaluation F ▷ G ≫ (λ_ G).hom

/-- `sheafTrace` is the evaluation contraction after inverting `Dual.tensorComparison`. -/
theorem sheafTrace_spec {k : Type u} [Field k] {d : ℕ}
    (F G : (scheme k d).Modules) [IsFiniteLocallyFree F] :
    Dual.tensorComparison F (F ⊗ G) ≫ sheafTrace F G =
      (β_ (F ⊗ G) (dual F)).hom ≫ (α_ (dual F) F G).inv ≫ Dual.evaluation F ▷ G ≫ (λ_ G).hom :=
  sorry

/-- Internal Hom on `scheme k d` is `k`-linear. -/
instance instLinear_ihom {k : Type u} [Field k] {d : ℕ} (F : (scheme k d).Modules) :
    (ihom F).Linear k := sorry

/-- Ext-level generalized trace `Ext F (F ⊗ G) i →ₗ Ext (𝟙_) G i`, obtained by internal-Hom
transport, precomposition with the identity section, and postcomposition with `sheafTrace`. -/
def extTrace {k : Type u} [Field k] {d : ℕ} [HasExt (scheme k d).Modules]
    (F G : (scheme k d).Modules) [IsFiniteLocallyFree F] (i : ℕ) :
    Ext F (F ⊗ G) i →ₗ[k] Ext (𝟙_ (scheme k d).Modules) G i :=
  (Ext.mk₀ (sheafTrace F G)).postcompOfLinear k (𝟙_ (scheme k d).Modules)
      (add_zero i) ∘ₗ
    (Ext.mk₀ (curry' (𝟙 F))).precompOfLinear k ((ihom F).obj (F ⊗ G))
      (zero_add i) ∘ₗ
      (ihom F).mapExtLinearMap k F (F ⊗ G) i

/-- In degree zero, `extTrace` is compatible with `linearEquiv₀` and `sheafTrace`. -/
theorem extTrace_zero {k : Type u} [Field k] {d : ℕ} [HasExt (scheme k d).Modules]
    (F G : (scheme k d).Modules) [IsFiniteLocallyFree F] (f : F ⟶ F ⊗ G) :
    extTrace F G 0 (Ext.mk₀ f) =
      Ext.mk₀ (curry' (𝟙 F) ≫ (ihom F).map f ≫ sheafTrace F G) := sorry

/-- The composite pairing of cup product followed by Ext-trace, with values in
`Ext (𝟙_) (omega k d) d`. -/
def extCupProductTracePairing {k : Type u} [Field k] {d : ℕ} [HasExt (scheme k d).Modules]
    (E F : (scheme k d).Modules) [IsFiniteLocallyFree F] (i : ℕ) (hi : i ≤ d) :
    Ext E (F ⊗ omega k d) i →ₗ[k]
      Ext F E (d - i) →ₗ[k] Ext (𝟙_ (scheme k d).Modules) (omega k d) d :=
  (cupProductPairing E F i hi).compr₂ (extTrace F (omega k d) d)

/-- The groups `Ext E (F ⊗ omega k d) i` are finite-dimensional `k`-vector spaces. -/
instance instFiniteDimensional_ext_omega {k : Type u} [Field k] {d : ℕ}
    [HasExt (scheme k d).Modules] (E F : (scheme k d).Modules)
    [IsFiniteLocallyFree E] [IsFiniteLocallyFree F] (i : ℕ) :
    FiniteDimensional k (Ext E (F ⊗ omega k d) i) := sorry

/-- The groups `Ext F E i` are finite-dimensional `k`-vector spaces. -/
instance instFiniteDimensional_ext_dual {k : Type u} [Field k] {d : ℕ}
    [HasExt (scheme k d).Modules] (E F : (scheme k d).Modules)
    [IsFiniteLocallyFree E] [IsFiniteLocallyFree F] (i : ℕ) :
    FiniteDimensional k (Ext F E i) := sorry

/-- Top-degree Ext of the dualizing sheaf on `scheme k d` is one-dimensional, so
`H^d(X, omega k d) = k`. -/
theorem omega_topExt_finrank {k : Type u} [Field k] (d : ℕ) [HasExt (scheme k d).Modules] :
    Module.finrank k (Ext (𝟙_ (scheme k d).Modules) (omega k d) d) = 1 := sorry

/-- Exercise 111.48.6: for a field `k`, `X = scheme k d`, and finite locally free `𝒪_X`-modules
`E`, `F`, the cup product
`Ext E (F ⊗ omega k d) i × Ext F E (d - i) → Ext F (F ⊗ omega k d) d`
followed by the Ext-trace to `Ext (𝟙_) (omega k d) d ≅ H^d(X, omega k d) = k` is a
nondegenerate `k`-pairing. -/
@[stacks 0DD6]
theorem extCupProduct_trace_nondegenerate {k : Type u} [Field k] (d i : ℕ) (hi : i ≤ d)
    (E F : (scheme k d).Modules) [IsFiniteLocallyFree E] [IsFiniteLocallyFree F]
    [HasExt (scheme k d).Modules] :
    Function.Bijective (extCupProductTracePairing E F i hi) ∧
      Function.Bijective (extCupProductTracePairing E F i hi).flip := sorry

end AlgebraicGeometry.ProjectiveSpace
