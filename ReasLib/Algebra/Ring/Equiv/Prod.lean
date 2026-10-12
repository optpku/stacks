/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Product ring equivalences

This leaf adds the ring and algebra forms of splitting a dependent product at
one chosen coordinate. Mathlib owns the underlying type equivalence
`Equiv.piSplitAt`; the declarations below retain its ring structure and expose
the projection and scalar-transport formulas needed by product decompositions.
-/

universe u v w x y

namespace RingEquiv.Pi

variable {ι : Type u}

/-- Split a dependent product of rings into a chosen coordinate and the product of all remaining
coordinates. This is the `RingEquiv` refinement of `Equiv.piSplitAt`. -/
def splitAt [DecidableEq ι] (i : ι) (Y : ι → Type v)
    [∀ j, NonAssocSemiring (Y j)] :
    (∀ j, Y j) ≃+* Y i × ((j : { j : ι // j ≠ i }) → Y j.1) where
  toEquiv := Equiv.piSplitAt i Y
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The first projection of `splitAt` is evaluation at the selected coordinate. -/
@[simp]
theorem splitAt_fst [DecidableEq ι] (i : ι) (Y : ι → Type v)
    [∀ j, NonAssocSemiring (Y j)] (z : ∀ j, Y j) :
    RingHom.fst (Y i) ((j : { j : ι // j ≠ i }) → Y j.1) (splitAt i Y z) = z i := sorry

/-- After a ring equivalence into a dependent product, the first projection of the selected
coordinate split is the corresponding coordinate of the original equivalence. -/
theorem trans_splitAt_fst {Y : ι → Type v} {T : Type w} [NonAssocSemiring T]
    [DecidableEq ι] [∀ j, NonAssocSemiring (Y j)]
    (E : T ≃+* ∀ j, Y j) (i : ι) (z : T) :
    RingHom.fst (Y i) ((j : { j : ι // j ≠ i }) → Y j.1)
        ((E.trans (splitAt i Y)) z) = E z i := sorry

/-- Transporting a product equivalence along equivalences of both factors transports its first
projection along the first factor equivalence. -/
theorem trans_prodCongr_fst
    {T : Type u} {A : Type v} {B : Type w} {C : Type x} {D : Type y}
    [NonAssocSemiring T] [NonAssocSemiring A] [NonAssocSemiring B]
    [NonAssocSemiring C] [NonAssocSemiring D]
    (E : T ≃+* (A × B)) (e₁ : A ≃+* C) (e₂ : B ≃+* D) (z : T) :
    RingHom.fst C D ((E.trans (RingEquiv.prodCongr e₁ e₂)) z) =
      e₁ (RingHom.fst A B (E z)) := sorry

/-- Splitting a dependent-product target at one coordinate and transporting that coordinate
along `e₁` has first projection `e₁` applied to the original coordinate. -/
theorem trans_splitAt_prodCongr_fst {Y : ι → Type v} {T : Type w} {C : Type x}
    [NonAssocSemiring T] [DecidableEq ι]
    [∀ j, NonAssocSemiring (Y j)] [NonAssocSemiring C]
    (E : T ≃+* ∀ j, Y j) (i : ι) (e₁ : Y i ≃+* C) (z : T) :
    RingHom.fst C ((j : { j : ι // j ≠ i }) → Y j.1)
        (((E.trans (splitAt i Y)).trans
          (RingEquiv.prodCongr e₁
            (RingEquiv.refl ((j : { j : ι // j ≠ i }) → Y j.1)))) z) =
      e₁ (E z i) := sorry

end RingEquiv.Pi

namespace RingEquiv.Prod

variable {K : Type u} {T : Type v} {C : Type w} {B : Type x}
variable [CommSemiring K] [Semiring T] [CommSemiring C] [CommSemiring B]
variable [Algebra K T]

/-- The canonical `K`-algebra structure on the second factor of a ring equivalence
`T ≃+* C × B`, obtained by transporting the scalar map through the second projection. -/
def secondAlgebra (E : T ≃+* (C × B)) : Algebra K B :=
  (((RingHom.snd C B).comp E.toRingHom).comp (algebraMap K T)).toAlgebra

/-- The scalar map of `secondAlgebra E` is the composite of the source scalar map, `E`, and the
second product projection. -/
theorem algebraMap_secondAlgebra (E : T ≃+* (C × B)) :
    @algebraMap K B _ _ (secondAlgebra E) =
      ((RingHom.snd C B).comp E.toRingHom).comp (algebraMap K T) := sorry

/-- If the first projection of `E` is the algebra map `π`, then after installing
`E.secondAlgebra` the ring equivalence commutes with the product `K`-algebra maps. -/
theorem map_algebraMap_eq_prod
    [Algebra K C]
    (π : T →ₐ[K] C) (E : T ≃+* (C × B))
    (hfst : ∀ z : T, RingHom.fst C B (E z) = π z) :
    letI : Algebra K B := secondAlgebra E
    ∀ k : K, E (algebraMap K T k) = algebraMap K (C × B) k := sorry

end RingEquiv.Prod
