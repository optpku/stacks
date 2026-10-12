/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import stacks_project.Chap97.«97_13_0_2_FreeDimAlgebra»

/-!
# The unit-fixing subgroup of GL_d

For a commutative ring `R` and `d ≥ 1`, `glFixOne R d` is the subgroup of
invertible `R`-linear automorphisms of `Fin d → R` that fix the unit vector
`FreeDimAlgebra.one R d`.
-/

@[expose] public section

noncomputable section

universe u

open Matrix

namespace AlgebraicGeometry

/-- The subgroup of `LinearMap.GeneralLinearGroup R (Fin d → R)` consisting of
automorphisms that fix `FreeDimAlgebra.one R d`. -/
def glFixOne (R : Type u) [CommRing R] (d : ℕ) [NeZero d] :
    Subgroup (LinearMap.GeneralLinearGroup R (Fin d → R)) where
  carrier := {g | g.val (FreeDimAlgebra.one R d) = FreeDimAlgebra.one R d}
  mul_mem' := sorry
  one_mem' := sorry
  inv_mem' := sorry

namespace GLFixOne

/-- Membership in `glFixOne R d` is the condition of fixing `FreeDimAlgebra.one R d`. -/
theorem mem_iff {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    (g : LinearMap.GeneralLinearGroup R (Fin d → R)) :
    g ∈ glFixOne R d ↔ g.val (FreeDimAlgebra.one R d) = FreeDimAlgebra.one R d :=
  sorry

/-- A ring homomorphism induces a group homomorphism on unit-fixing general linear groups,
via the matrix representation of the underlying automorphism. -/
def map {R S : Type u} [CommRing R] [CommRing S] {d : ℕ} [NeZero d] (f : R →+* S) :
    glFixOne R d →* glFixOne S d where
  toFun g :=
    ⟨GeneralLinearGroup.toLin
      (GeneralLinearGroup.map f (GeneralLinearGroup.toLin.symm g.val)), sorry⟩
  map_one' := sorry
  map_mul' := sorry

/-- `map f` applies `Matrix.GeneralLinearGroup.map f` to the underlying automorphism. -/
theorem map_apply {R S : Type u} [CommRing R] [CommRing S] {d : ℕ} [NeZero d]
    (f : R →+* S) (g : glFixOne R d) :
    (map f g).val =
      GeneralLinearGroup.toLin
        (GeneralLinearGroup.map f (GeneralLinearGroup.toLin.symm g.val)) :=
  sorry

/-- `map f` preserves the identity automorphism. -/
theorem map_one {R S : Type u} [CommRing R] [CommRing S] {d : ℕ} [NeZero d] (f : R →+* S) :
    map f (1 : glFixOne R d) = 1 :=
  sorry

end GLFixOne

end AlgebraicGeometry
