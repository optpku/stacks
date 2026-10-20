/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.BaseChange
public import ReasLib.RingTheory.RingHom.PowerImage
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change for power-image generation

@stack 0EUH

The primary statements take the two ring homomorphisms defining a tensor-product
base change. Ambient-algebra specializations are separate conveniences for
callers whose tensor-product instances are already fixed.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace PowerImage

namespace BaseChange

/-- Power-image generation is preserved by tensor-product base change along an arbitrary ring
homomorphism. -/
theorem isGenerated
    {R' : Type w} [CommRing R'] {E : Set ℕ}
    (f : R →+* S) (g : R →+* R') (hgen : PowerImage.IsGenerated f E) :
    PowerImage.IsGenerated (f.baseChange g) E := sorry

/-- Ambient-algebra specialization of the BaseChange.isGenerated theorem. -/
theorem isGenerated_algebraMap
    {R' : Type w} [CommRing R'] [Algebra R R'] [Algebra R S] {E : Set ℕ}
    (hgen : PowerImage.IsGenerated (algebraMap R S) E) :
    PowerImage.IsGenerated (algebraMap R' (R' ⊗[R] S)) E := sorry

end BaseChange

namespace Pair

namespace BaseChange

/-- Two-power image generation is preserved by tensor-product base change along an arbitrary ring
homomorphism. -/
theorem isGenerated
    {R' : Type w} [CommRing R'] {m n : ℕ}
    (f : R →+* S) (g : R →+* R') (hgen : Pair.IsGenerated f m n) :
    Pair.IsGenerated (f.baseChange g) m n := sorry

/-- Ambient-algebra specialization of the Pair.BaseChange.isGenerated theorem. -/
theorem isGenerated_algebraMap
    {R' : Type w} [CommRing R'] [Algebra R R'] [Algebra R S] {m n : ℕ}
    (hgen : Pair.IsGenerated (algebraMap R S) m n) :
    Pair.IsGenerated (algebraMap R' (R' ⊗[R] S)) m n := sorry

end BaseChange

end Pair

namespace SquareCube

namespace BaseChange

/-- Square/cube image generation is preserved by tensor-product base change along an arbitrary
ring homomorphism. -/
@[stacks 0EUH]
theorem isGenerated
    {R' : Type w} [CommRing R']
    (f : R →+* S) (g : R →+* R') (hgen : SquareCube.IsGenerated f) :
    SquareCube.IsGenerated (f.baseChange g) := sorry

/-- Ambient-algebra specialization of the SquareCube.BaseChange.isGenerated theorem. -/
theorem isGenerated_algebraMap
    {R' : Type w} [CommRing R'] [Algebra R R'] [Algebra R S]
    (hgen : SquareCube.IsGenerated (algebraMap R S)) :
    SquareCube.IsGenerated (algebraMap R' (R' ⊗[R] S)) := sorry

end BaseChange

end SquareCube

end PowerImage

end RingHom
