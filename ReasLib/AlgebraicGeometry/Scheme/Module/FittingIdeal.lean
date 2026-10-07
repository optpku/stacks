module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.RingTheory.FittingIdeal

/-!
# Fitting ideal sheaves of scheme modules

This leaf turns the affine Fitting ideals of a scheme module into canonical
`IdealSheafData`. Finiteness and quasi-coherence enter the comparison API,
not the concrete data owner, so the sheaf construction does not depend on a
proof of finite generation.
-/

@[expose] public section

open AlgebraicGeometry
open scoped FittingIdeal

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The `i`th Fitting ideal sheaf of a scheme module, obtained from the family of intrinsic
Fitting ideals of its affine section modules. The underlying family is total; finite type and
quasi-coherence are needed only to identify its affine components with that family. -/
def fittingIdealSheaf
    {S : Scheme.{u}} (ℱ : S.Modules) (i : ℕ) :
    S.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals fun U ↦
    Fit[Γ(S, U)]_(i)(Γ(ℱ, (U : S.Opens)))

/-- On an affine open, `fittingIdealSheaf` is the ordinary Fitting ideal of the corresponding
module of sections when the sheaf is finite type and quasi-coherent. -/
@[simp]
theorem fittingIdealSheaf_ideal
    {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    (i : ℕ) (U : S.affineOpens) :
    (fittingIdealSheaf ℱ i).ideal U =
      Fit[Γ(S, U)]_(i)(Γ(ℱ, (U : S.Opens))) := sorry

/-- The Fitting ideal sheaf one step below the indicated rank, with the predecessor of the
zeroth Fitting ideal sheaf defined to be the zero ideal sheaf. -/
abbrev precedingFittingIdealSheaf
    {S : Scheme.{u}} (ℱ : S.Modules) (r : ℕ) :
    S.IdealSheafData :=
  match r with
  | 0 => ⊥
  | r + 1 => fittingIdealSheaf ℱ r

/-- The predecessor of the zeroth Fitting ideal sheaf is the zero ideal sheaf. -/
@[simp]
theorem precedingFittingIdealSheaf_zero
    {S : Scheme.{u}} (ℱ : S.Modules) :
    precedingFittingIdealSheaf ℱ 0 = ⊥ :=
  rfl

/-- The predecessor of the `(r + 1)`st Fitting ideal sheaf is the `r`th Fitting ideal sheaf. -/
@[simp]
theorem precedingFittingIdealSheaf_succ
    {S : Scheme.{u}} (ℱ : S.Modules) (r : ℕ) :
    precedingFittingIdealSheaf ℱ (r + 1) = fittingIdealSheaf ℱ r :=
  rfl

/-- On an affine open, the predecessor Fitting ideal sheaf is the predecessor Fitting ideal of
the corresponding module of sections. -/
@[simp]
theorem precedingFittingIdealSheaf_ideal
    {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    (r : ℕ) (U : S.affineOpens) :
    (precedingFittingIdealSheaf ℱ r).ideal U =
      precedingFittingIdeal (Γ(S, U)) (Γ(ℱ, U)) r := sorry

end AlgebraicGeometry.Scheme
