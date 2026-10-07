module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Linearity
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Ext cup-product and trace pairings over a field

Yoneda composition supplies a concrete `k`-bilinear pairing of Ext groups on a scheme over `k`.
Postcomposition with a supplied trace yields the corresponding pairing with values in `k`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- The canonical `k`-linear structure on modules over a scheme over `k`, induced by the
structure morphism. -/
noncomputable instance instLinearModules {k : Type u} [Field k] (X : SchemeOverField k) :
    Linear k (X.left.Modules) :=
  Scheme.Modules.baseLinear X.hom

/-- The `k`-linear Yoneda cup-product pairing
`Ext F ω i →ₗ Ext (𝟙_) F (d - i) →ₗ Ext (𝟙_) ω d`. -/
noncomputable def yonedaPairing {k : Type u} [Field k] (X : SchemeOverField k)
    [HasExt (X.left.Modules)] (ω F : X.left.Modules) {i d : ℕ} (hi : i ≤ d) :
    Ext F ω i →ₗ[k] Ext (𝟙_ (X.left.Modules)) F (d - i) →ₗ[k]
      Ext (𝟙_ (X.left.Modules)) ω d :=
  (Ext.bilinearCompOfLinear k (𝟙_ (X.left.Modules)) F ω (d - i) i d
      (Nat.sub_add_cancel hi)).flip

/-- `yonedaPairing` evaluates as Yoneda composition `β.comp α`. -/
theorem yonedaPairing_apply {k : Type u} [Field k] (X : SchemeOverField k)
    [HasExt (X.left.Modules)] {ω F : X.left.Modules} {i d : ℕ} (hi : i ≤ d)
    (α : Ext F ω i) (β : Ext (𝟙_ (X.left.Modules)) F (d - i)) :
    yonedaPairing X ω F hi α β = β.comp α (Nat.sub_add_cancel hi) :=
  sorry

/-- The composition of `yonedaPairing` with a supplied trace
`Ext (𝟙_) ω d →ₗ[k] k`. -/
noncomputable def tracePairing {k : Type u} [Field k] (X : SchemeOverField k)
    [HasExt (X.left.Modules)] {ω : X.left.Modules} {d : ℕ}
    (t : Ext (𝟙_ (X.left.Modules)) ω d →ₗ[k] k) (F : X.left.Modules) {i : ℕ}
    (hi : i ≤ d) :
    Ext F ω i →ₗ[k] Ext (𝟙_ (X.left.Modules)) F (d - i) →ₗ[k] k :=
  (yonedaPairing X ω F hi).compr₂ t

/-- `tracePairing` is postcomposition of `yonedaPairing` with the supplied trace. -/
theorem tracePairing_def {k : Type u} [Field k] (X : SchemeOverField k)
    [HasExt (X.left.Modules)] {ω : X.left.Modules} {d : ℕ}
    (t : Ext (𝟙_ (X.left.Modules)) ω d →ₗ[k] k) (F : X.left.Modules) {i : ℕ}
    (hi : i ≤ d) :
    tracePairing X t F hi = (yonedaPairing X ω F hi).compr₂ t :=
  sorry

/-- Evaluation of `tracePairing` is the trace of the Yoneda pairing. -/
theorem tracePairing_apply {k : Type u} [Field k] (X : SchemeOverField k)
    [HasExt (X.left.Modules)] {ω : X.left.Modules} {d : ℕ}
    (t : Ext (𝟙_ (X.left.Modules)) ω d →ₗ[k] k) (F : X.left.Modules) {i : ℕ}
    (hi : i ≤ d) (α : Ext F ω i) (β : Ext (𝟙_ (X.left.Modules)) F (d - i)) :
    tracePairing X t F hi α β = t (yonedaPairing X ω F hi α β) :=
  sorry

end AlgebraicGeometry.SchemeOverField
