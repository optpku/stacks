/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restricting Ring Homomorphisms to Ideals

A ring homomorphism carrying one ideal into another restricts to a non-unital
ring homomorphism between the ideals.  The kernel and mapped-ideal
constructions below are the two standard commuting-square specializations.

@stack 05YT
-/

@[expose] public section

universe uR uS uT uB

namespace RingHom

variable {S : Type uS} {T : Type uT} [Semiring S] [Semiring T]

/-- Restrict a ring homomorphism to a pair of ideals that it preserves. -/
@[stacks 05YT "restriction of a ring homomorphism to ideals"]
def restrictIdeals (phi : S →+* T) {I : Ideal S} {J : Ideal T}
    (h : I ≤ J.comap phi) : I →ₙ+* J :=
  NonUnitalRingHom.codRestrict
    (phi.toNonUnitalRingHom.comp (NonUnitalSubsemiringClass.subtype I)) J
    (fun x ↦ h x.2)

@[simp]
theorem coe_restrictIdeals (phi : S →+* T) {I : Ideal S} {J : Ideal T}
    (h : I ≤ J.comap phi) (x : I) :
    (restrictIdeals phi h x : T) = phi x :=
  rfl

variable {B : Type uB} [Semiring B]

/-- A commuting triangle induces a non-unital ring homomorphism on kernels. -/
@[stacks 05YT "map on kernels induced by a commuting triangle"]
def kerMap {qS : S →+* B} {qT : T →+* B} (phi : S →+* T)
    (h : qT.comp phi = qS) : RingHom.ker qS →ₙ+* RingHom.ker qT :=
  restrictIdeals phi (by rw [RingHom.comap_ker, h])

@[simp]
theorem coe_kerMap {qS : S →+* B} {qT : T →+* B} (phi : S →+* T)
    (h : qT.comp phi = qS) (x : RingHom.ker qS) :
    (kerMap phi h x : T) = phi x :=
  rfl

end RingHom

namespace Ideal

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [Semiring R] [Semiring S] [Semiring T]

/-- In a commuting triangle, the image of an ideal in the intermediate ring
maps into its image in the target ring. -/
@[stacks 05YT "mapped ideals in a commuting triangle"]
theorem map_le_comap_of_comp_eq (I : Ideal R) {f : R →+* S} {g : R →+* T}
    (phi : S →+* T) (h : phi.comp f = g) :
    I.map f ≤ (I.map g).comap phi := by
  rw [← Ideal.map_le_iff_le_comap]
  simpa only [Ideal.map_map, h] using (le_refl (I.map g))

/-- The non-unital ring homomorphism between mapped ideals induced by a
commuting triangle. -/
@[stacks 05YT "map between ideal images in a commuting triangle"]
def mapMap (I : Ideal R) {f : R →+* S} {g : R →+* T}
    (phi : S →+* T) (h : phi.comp f = g) : I.map f →ₙ+* I.map g :=
  RingHom.restrictIdeals phi (map_le_comap_of_comp_eq I phi h)

@[simp]
theorem coe_mapMap (I : Ideal R) {f : R →+* S} {g : R →+* T}
    (phi : S →+* T) (h : phi.comp f = g) (x : I.map f) :
    (mapMap I phi h x : T) = phi x :=
  rfl

end Ideal
