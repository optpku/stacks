module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal

/-!
# External tensor products of scheme modules

This leaf owns the canonical external tensor product on a fiber product of
schemes.  It is independent of the base being a field.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The external tensor product `p₁^*ℱ ⊗ p₂^*𝒢` on the fiber product of two schemes over `S`. -/
abbrev externalTensorProduct
    {X S Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    (F : X.Modules) (G : Y.Modules) :
    (Limits.pullback a b).Modules :=
  tensorObj
    ((Scheme.Modules.pullback (Limits.pullback.fst a b)).obj F)
    ((Scheme.Modules.pullback (Limits.pullback.snd a b)).obj G)

end AlgebraicGeometry.Scheme.Modules
