/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.ConormalSequence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth
import Mathlib.Tactic.CrossRefAttribute

/-!
# Short exactness of conormal sequences under formal smoothness

For a formally unramified morphism of algebraic spaces over a base, formal
smoothness of its domain over that base makes the canonical conormal sequence
short exact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
namespace Differentials

variable {S : Scheme.{u}} {B X Z Z' : AlgebraicSpace S}
variable (i : Z ⟶ Z') (h' : Z' ⟶ X) (h : Z ⟶ X) (f : X ⟶ B)
variable [IsUniversalFirstOrder i h'] [FormallyUnramified h]
variable [FormallySmooth (h ≫ f)]
variable (w : i ≫ h' = h)

/-- For a formally unramified morphism `h : Z ⟶ X` of algebraic spaces over `B`,
formal smoothness of `Z` over `B` makes the canonical conormal sequence,
presented by a universal first-order thickening, short exact. -/
@[stacks 06BJ]
theorem shortExact_of_formallySmooth :
    (complex i h' h f w).ShortExact := sorry

/-- For a formally unramified morphism `h : Z ⟶ X` with `Z` formally smooth
over `B`, the canonical conormal map `C_{Z/X} ⟶ h^* Ω_{X/B}` is a
monomorphism. -/
instance mono_conormalMap : Mono (conormalMap i h' h f w) := sorry

end Differentials
end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
