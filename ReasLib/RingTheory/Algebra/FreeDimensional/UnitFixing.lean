/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebra.FreeDimensional
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
open AlgebraicGeometry Matrix
noncomputable section
universe u

namespace AlgebraicGeometry

/-- The subgroup of general linear automorphisms fixing the distinguished unit. -/
def glFixOne (R : Type u) [CommRing R] (d : ℕ) [NeZero d] :
    Subgroup (LinearMap.GeneralLinearGroup R (Fin d → R)) :=
  MulAction.stabilizer (LinearMap.GeneralLinearGroup R (Fin d → R)) (FreeDimAlgebra.one R d)

namespace GLFixOne

/-- Membership in the unit-fixing subgroup is the fixed-point condition. -/
theorem mem_iff {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    (g : LinearMap.GeneralLinearGroup R (Fin d → R)) :
    g ∈ glFixOne R d ↔ g • FreeDimAlgebra.one R d = FreeDimAlgebra.one R d :=
  MulAction.mem_stabilizer_iff

private theorem map_mem {R S : Type u} [CommRing R] [CommRing S] {d : ℕ} [NeZero d]
    (f : R →+* S) (g : glFixOne R d) :
    GeneralLinearGroup.toLin (GeneralLinearGroup.map f (GeneralLinearGroup.toLin.symm g.val)) •
        FreeDimAlgebra.one S d = FreeDimAlgebra.one S d := sorry

/-- Base change of coefficients induces a homomorphism of unit-fixing groups. -/
def map {R S : Type u} [CommRing R] [CommRing S] {d : ℕ} [NeZero d] (f : R →+* S) :
    glFixOne R d →* glFixOne S d where
  toFun g :=
    ⟨GeneralLinearGroup.toLin
      (GeneralLinearGroup.map f (GeneralLinearGroup.toLin.symm g.val)), map_mem f g⟩
  map_one' := by
    ext x
    simp [Matrix.GeneralLinearGroup.map_apply]
  map_mul' g h := by
    ext x
    simp [Matrix.GeneralLinearGroup.map_apply]

/-- The underlying general linear map of `map f g` is the coefficientwise matrix map. -/
theorem map_apply {R S : Type u} [CommRing R] [CommRing S] {d : ℕ} [NeZero d]
    (f : R →+* S) (g : glFixOne R d) :
    (map f g).val =
      GeneralLinearGroup.toLin
        (GeneralLinearGroup.map f (GeneralLinearGroup.toLin.symm g.val)) :=
  rfl

end GLFixOne
end AlgebraicGeometry
