module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Trace
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# Scalar-linear trace on Ext

Internal Hom, the identity section, and evaluation contraction define a scalar-linear trace
with values in Ext from the tensor unit.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace AlgebraicGeometry.RingedSpace.Module.Trace

variable (R : Type v) [CommRing R] {X : RingedSpace.{u}}
    [linear : Linear R X.Modules] [HasExt X.Modules]

/-- The scalar-linear generalized trace on Ext, valued in Ext from the tensor unit. -/
def extLinear (E G : X.Modules) [E.IsFiniteLocallyFree] [ihomLinear : (ihom E).Linear R]
    (i : ℕ) :
    Ext E (E ⊗ G) i →ₗ[R] Ext (𝟙_ X.Modules) G i :=
  (Ext.mk₀ (sheaf E G)).postcompOfLinear R (𝟙_ X.Modules) (add_zero i) ∘ₗ
    (Ext.mk₀ (identitySection E)).precompOfLinear R ((ihom E).obj (E ⊗ G))
      (zero_add i) ∘ₗ
      (ihom E).mapExtLinearMap R E (E ⊗ G) i

/-- In degree zero, the linear trace is induced by the sheaf-level evaluation contraction. -/
theorem extLinear_mk₀ (E G : X.Modules) [E.IsFiniteLocallyFree] [(ihom E).Linear R]
    (f : E ⟶ E ⊗ G) :
    extLinear R E G 0 (Ext.mk₀ f) =
      Ext.mk₀ (identitySection E ≫ (ihom E).map f ≫ sheaf E G) := sorry

/-- Transport from the tensor unit to the structure module recovers the additive Ext trace. -/
theorem extLinear_unitComparison (E G : X.Modules) [E.IsFiniteLocallyFree]
    [(ihom E).Linear R] (i : ℕ) (α : Ext E (E ⊗ G) i) :
    (Ext.mk₀ (unitIsoTensorUnit X).hom).comp (extLinear R E G i α) (zero_add i) =
      ext E G i α := by
  rfl

end AlgebraicGeometry.RingedSpace.Module.Trace
