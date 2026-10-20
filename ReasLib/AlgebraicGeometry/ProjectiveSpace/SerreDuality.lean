module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Linear
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Trace.Linear
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Serre duality on projective space

Yoneda composition followed by trace gives a perfect pairing with values in the top
cohomology of the dualizing twist.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The dualizing sheaf of projective `d`-space is the twist of degree `-d - 1`. -/
abbrev omega (k : Type u) [Field k] (d : ℕ) : (scheme k d).Modules :=
  twistingSheaf k d (-(d : ℤ) - 1)

/-- Yoneda composition followed by trace, valued in top Ext from the tensor unit. -/
def extCupProductTracePairing {k : Type u} [Field k] {d : ℕ} [HasExt (scheme k d).Modules]
    (E F : (scheme k d).Modules) [IsFiniteLocallyFree F] (i : ℕ) (hi : i ≤ d) :
    Ext E (F ⊗ omega k d) i →ₗ[k]
      Ext F E (d - i) →ₗ[k] Ext (𝟙_ (scheme k d).Modules) (omega k d) d :=
  ((Ext.bilinearCompOfLinear k F E (F ⊗ omega k d) (d - i) i d
      (Nat.sub_add_cancel hi)).flip).compr₂
    (RingedSpace.Module.Trace.extLinear k (linear := instLinearModules k d)
      F (omega k d) (ihomLinear := instLinear_ihom F) d)

/-- The cup-product trace pairing evaluates by first composing the two Ext classes. -/
theorem extCupProductTracePairing_apply {k : Type u} [Field k] {d : ℕ}
    [HasExt (scheme k d).Modules] {E F : (scheme k d).Modules} [IsFiniteLocallyFree F]
    {i : ℕ} (hi : i ≤ d) (α : Ext E (F ⊗ omega k d) i) (β : Ext F E (d - i)) :
    extCupProductTracePairing E F i hi α β =
      RingedSpace.Module.Trace.extLinear k (linear := instLinearModules k d)
        F (omega k d) (ihomLinear := instLinear_ihom F) d
        (β.comp α (Nat.sub_add_cancel hi)) := by
  rfl

/-- Ext into a finite locally free module tensored with the dualizing sheaf is finite-dimensional.
-/
instance instFiniteDimensional_ext_omega {k : Type u} [Field k] {d : ℕ}
    [HasExt (scheme k d).Modules] (E F : (scheme k d).Modules)
    [IsFiniteLocallyFree E] [IsFiniteLocallyFree F] (i : ℕ) :
    FiniteDimensional k (Ext E (F ⊗ omega k d) i) := sorry

/-- Ext between finite locally free modules on projective space is finite-dimensional. -/
instance instFiniteDimensional_ext_dual {k : Type u} [Field k] {d : ℕ}
    [HasExt (scheme k d).Modules] (E F : (scheme k d).Modules)
    [IsFiniteLocallyFree E] [IsFiniteLocallyFree F] (i : ℕ) :
    FiniteDimensional k (Ext F E i) := sorry

/-- The top cohomology of the dualizing sheaf, expressed as Ext from the tensor unit,
is one-dimensional. -/
theorem omega_topExt_finrank {k : Type u} [Field k] (d : ℕ) [HasExt (scheme k d).Modules] :
    Module.finrank k (Ext (𝟙_ (scheme k d).Modules) (omega k d) d) = 1 := sorry

/-- Cup product followed by trace gives a perfect pairing between complementary Ext groups
of finite locally free modules on projective space, valued in the top cohomology of the
dualizing sheaf. -/
theorem extCupProduct_trace_nondegenerate {k : Type u} [Field k] (d i : ℕ) (hi : i ≤ d)
    (E F : (scheme k d).Modules) [IsFiniteLocallyFree E] [IsFiniteLocallyFree F]
    [HasExt (scheme k d).Modules] :
    Function.Bijective (extCupProductTracePairing E F i hi) ∧
      Function.Bijective (extCupProductTracePairing E F i hi).flip := sorry

end AlgebraicGeometry.ProjectiveSpace
