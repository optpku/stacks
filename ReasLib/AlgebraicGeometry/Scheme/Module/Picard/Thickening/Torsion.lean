/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

@[expose] public section

open CategoryTheory AddSubgroup
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsThickening

variable {X X' : Scheme.{u}} (i : X ⟶ X') [IsThickening i]

/-- Pullback along a thickening bijects the `n`-torsion Picard subgroups if `n` is
invertible and global units lift modulo `n`th powers along the canonical map `i.appTop`.

The units hypothesis says that the induced map on global units modulo `n`th powers
is surjective. The Kummer sequences and invariance of etale `μ_n`-torsors under
thickenings then give the claimed bijection. Without this hypothesis the cokernel
of that units map is the kernel on Picard torsion: invertibility of `n` on the
cohomology of the nilpotent ideal does not remove this global-unit obstruction.
This corrects the missing hypothesis in Stacks tag `0C6S`. -/
theorem picardPullback_bijOn_torsionBy (n : ℤ)
    (h_unit : IsUnit (n : Γ(X, ⊤)))
    (h_units : ∀ u : Γ(X, ⊤)ˣ, ∃ u' : Γ(X', ⊤)ˣ, ∃ v : Γ(X, ⊤)ˣ,
      u = Units.map i.appTop.hom.toMonoidHom u' * v ^ n) :
    Set.BijOn (Scheme.Hom.picardPullback i) X'.PicardGroup[n] X.PicardGroup[n] := sorry

end AlgebraicGeometry.IsThickening
