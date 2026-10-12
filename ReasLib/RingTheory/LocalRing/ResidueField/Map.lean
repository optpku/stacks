/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Maps and equivalences of residue fields

This file records the functoriality of residue-field maps and turns the
bijectivity of a residue-field map induced by a map surjective on stalks into
an algebra equivalence.  It also gives map-level properties of the residue map
of a local homomorphism without registering a competing residue-field algebra
instance.
-/

namespace Ideal.ResidueField

universe u v w

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- Residue-field maps induced by composable ring homomorphisms compose in the expected order. -/
theorem map_comp
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime] (K : Ideal C) [K.IsPrime]
    (f : A →+* B) (g : B →+* C)
    (hIJ : I = Ideal.comap f J) (hJK : J = Ideal.comap g K)
    (hIK : I = Ideal.comap (g.comp f) K) :
    (Ideal.ResidueField.map J K g hJK).comp (Ideal.ResidueField.map I J f hIJ) =
      Ideal.ResidueField.map I K (g.comp f) hIK := sorry

/-- A scalar tower from `R` through `κ(p)` into a field has kernel exactly
`p` on its structural map.  This is the ring-theoretic kernel fact behind
target constructions over a selected prime. -/
@[stacks 04GW "kernel of a scalar tower through a prime residue field"]
theorem ker_algebraMap_eq_of_scalarTower
    {p : Ideal R} [p.IsPrime] {K : Type w} [Field K]
    [Algebra R K] [Algebra p.ResidueField K]
    [IsScalarTower R p.ResidueField K] :
    RingHom.ker (algebraMap R K) = p := sorry

/-- A lift from an ideal residue field recovers the original ring map after
composition with the canonical map to that residue field. -/
@[simp]
theorem lift_comp_algebraMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (I : Ideal R) [I.IsPrime] (f : R →+* S)
    (hker_le : I ≤ RingHom.ker f)
    (hunit : I.primeCompl ≤ (IsUnit.submonoid S).comap f) :
    (Ideal.ResidueField.lift I f hker_le hunit).comp
        (algebraMap R I.ResidueField) = f := sorry

/-- The algebra structure on `κ(P)` over `κ(p)` induced by `P.LiesOver p` via the
canonical localized lying-over algebra. -/
@[stacks 04GW "residue-field algebra induced by lying over", implicit_reducible]
noncomputable def algebraOfLiesOver (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime]
    [P.LiesOver p] : Algebra p.ResidueField P.ResidueField :=
  -- Local instance justification (instance diamond): Mathlib deliberately keeps the localized
  -- lying-over algebra explicit because a global instance creates competing localization paths.
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime P) :=
    Localization.AtPrime.algebraOfLiesOver p P
  -- Local instance justification (proof-local temporary data): this records that the selected
  -- localized algebra is the canonical lying-over map used by the residue-field construction.
  letI : Localization.AtPrime.IsLiesOverAlgebra p P := inferInstance
  IsLocalRing.ResidueField.instAlgebra

/-- The algebra map of `algebraOfLiesOver` is the canonical map on ideal residue fields. -/
@[simp, stacks 04GW "algebra map of the lying-over residue-field algebra"]
theorem algebraMap_algebraOfLiesOver
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    -- Local instance justification (instance diamond): keep the branch-dependent residue algebra
    -- scoped to this statement instead of registering a competing global instance.
    letI : Algebra p.ResidueField P.ResidueField := algebraOfLiesOver p P
    algebraMap p.ResidueField P.ResidueField =
      Ideal.ResidueField.map p P (algebraMap R S) (Ideal.LiesOver.over) := by
  rfl

/-- The residue-field algebra induced by `P.LiesOver p` is compatible with every scalar tower
through the ambient algebra map. -/
@[stacks 04GW "scalar tower for a lying-over residue-field algebra"]
theorem isScalarTower_of_liesOver
    {K : Type w} [CommRing K] [Algebra K R] [Algebra K S] [IsScalarTower K R S]
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    -- Local instance justification (noncanonical choice): the residue-field algebra depends on
    -- the selected lying-over prime.
    letI : Algebra p.ResidueField P.ResidueField := algebraOfLiesOver p P
    IsScalarTower K p.ResidueField P.ResidueField := sorry

/-- The residue-field map of an algebra map surjective on stalks is an algebra
equivalence at corresponding prime ideals. -/
@[stacks 04GW "residue-field algebra equivalence from stalk surjectivity"]
noncomputable def mapAlgEquivOfSurjectiveOnStalks
    {K : Type u} {A : Type v} {B : Type w} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (f : A →ₐ[K] B)
    (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime]
    (hcomap : I = Ideal.comap f J) (hf : f.toRingHom.SurjectiveOnStalks) :
    I.ResidueField ≃ₐ[K] J.ResidueField :=
  AlgEquiv.ofBijective (Ideal.ResidueField.mapₐ I J f hcomap)
    (hf.residueFieldMap_bijective I J hcomap)

/-- For compatible ambient scalar towers, the canonical residue-field map at a lying-over
pair is the ambient `κ(p)`-algebra map. -/
@[stacks 04GW "lying-over residue-field map as an algebra map"]
theorem map_eq_algebraMap_of_liesOver
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra p.ResidueField q.ResidueField]
    [IsScalarTower R S q.ResidueField] [IsScalarTower R p.ResidueField q.ResidueField] :
    Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p) =
      algebraMap p.ResidueField q.ResidueField := by
  apply Ideal.ResidueField.ringHom_ext
  ext r
  simp only [RingHom.comp_apply]
  rw [Ideal.ResidueField.map_algebraMap]
  rw [← IsScalarTower.algebraMap_apply R S q.ResidueField]
  rw [← IsScalarTower.algebraMap_apply R p.ResidueField q.ResidueField]

/-- In a compatible ambient residue-field scalar tower, stalk-surjectivity makes the induced
`κ(p)`-algebra map to `κ(q)` bijective. -/
@[stacks 04GW "lying-over residue-field algebra-map bijectivity"]
theorem algebraMap_bijective_of_stalks
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra p.ResidueField q.ResidueField]
    [IsScalarTower R S q.ResidueField] [IsScalarTower R p.ResidueField q.ResidueField]
    (hf : (algebraMap R S).SurjectiveOnStalks) :
    Function.Bijective (algebraMap p.ResidueField q.ResidueField) := sorry

/-- The residue-field algebra equivalence induced by stalk-surjectivity in a compatible ambient
scalar tower. -/
@[stacks 04GW "lying-over residue-field algebra equivalence"]
noncomputable def algEquivOfStalks
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra p.ResidueField q.ResidueField]
    [IsScalarTower R S q.ResidueField] [IsScalarTower R p.ResidueField q.ResidueField]
    (hf : (algebraMap R S).SurjectiveOnStalks) :
    p.ResidueField ≃ₐ[p.ResidueField] q.ResidueField :=
  AlgEquiv.ofRingEquiv
    (f := (mapAlgEquivOfSurjectiveOnStalks (Algebra.ofId R S) p q
      (Ideal.over_def q p) hf).toRingEquiv)
    fun x => by
      change Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p) x =
        algebraMap p.ResidueField q.ResidueField x
      rw [map_eq_algebraMap_of_liesOver p q]

/-- For primes `p` and `q` with `q` lying over `p`, stalk-surjectivity of
`R → S` makes the canonical `κ(p)`-algebra map to `κ(q)` bijective. -/
@[stacks 04GW "lying-over residue-field algebra-map specialization"]
theorem algebraMap_bijective_of_surjectiveOnStalks
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hf : (algebraMap R S).SurjectiveOnStalks) :
    -- Local instance justification (noncanonical choice): the residue-field algebra depends on
    -- the selected lying-over prime.
    letI : Algebra p.ResidueField q.ResidueField := algebraOfLiesOver p q
    Function.Bijective (algebraMap p.ResidueField q.ResidueField) := sorry

/-- The `κ(p)`-algebra equivalence at a lying-over pair induced by a map
surjective on stalks. -/
@[stacks 04GW "lying-over residue-field equivalence specialization"]
noncomputable def algEquivOfSurjectiveOnStalks
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hf : (algebraMap R S).SurjectiveOnStalks) :
    -- Local instance justification (noncanonical choice): the residue-field algebra depends on
    -- the selected lying-over prime.
    letI : Algebra p.ResidueField q.ResidueField := algebraOfLiesOver p q
    p.ResidueField ≃ₐ[p.ResidueField] q.ResidueField :=
  -- Local instance justification (noncanonical choice): construct the equivalence using the
  -- algebra attached to this lying-over pair.
  letI : Algebra p.ResidueField q.ResidueField := algebraOfLiesOver p q
  AlgEquiv.ofRingEquiv
    (f := (mapAlgEquivOfSurjectiveOnStalks (Algebra.ofId R S) p q
      (Ideal.over_def q p) hf).toRingEquiv)
    fun x => by
      change Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p) x =
        algebraMap p.ResidueField q.ResidueField x
      rw [← algebraMap_algebraOfLiesOver p q]

end Ideal.ResidueField

namespace Ideal

universe u v

/-- If the kernel of a map to a field is `I`, then every element outside `I`
maps to a unit.  This is the unit hypothesis required by
`Ideal.ResidueField.lift`. -/
theorem primeCompl_le_isUnit_comap_of_ker_eq
    {R : Type u} {K : Type v} [CommRing R] [Field K]
    (I : Ideal R) [I.IsPrime] (f : R →+* K)
    (hker : RingHom.ker f = I) :
    I.primeCompl ≤ (IsUnit.submonoid K).comap f := sorry

end Ideal

namespace RingHom.ResidueField

universe u v

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

/-- The predicate that the residue-field map induced by a local ring
homomorphism is finite and purely inseparable. -/
noncomputable def FinitePurelyInseparable
    (f : R →+* S) (hlocal : IsLocalHom f) : Prop :=
  let fκ : IsLocalRing.ResidueField R →+* IsLocalRing.ResidueField S :=
    @IsLocalRing.ResidueField.map R S _ _ _ _ f hlocal
  fκ.Finite ∧ fκ.IsPurelyInseparable

/-- A bijective residue-field map induced by an explicit local ring homomorphism is purely
inseparable.  Localness remains an ordinary argument so this statement does not require callers
to install a temporary `IsLocalHom` instance. -/
theorem isPurelyInseparable_of_bijective
    (f : R →+* S) (hlocal : IsLocalHom f)
    (hbij : Function.Bijective (@IsLocalRing.ResidueField.map R S _ _ _ _ f hlocal)) :
    (@IsLocalRing.ResidueField.map R S _ _ _ _ f hlocal).IsPurelyInseparable := sorry

end RingHom.ResidueField

namespace AlgEquiv

universe u v

open IsLocalRing
open scoped TensorProduct

/-- A `p.ResidueField`-algebra equivalence from the fiber of `A` over `p` to
`p.ResidueField` sends `1 ⊗ₜ x` to the residue class of the image of `x` under an
`R`-algebra equivalence `A ≃ₐ[R] R`. -/
@[simp]
theorem residueField_apply_tmul
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {p : Ideal R} [p.IsPrime]
    (e : A ≃ₐ[R] R)
    (eκ : (p.ResidueField ⊗[R] A) ≃ₐ[p.ResidueField] p.ResidueField)
    (x : A) :
    eκ (1 ⊗ₜ[R] x) = algebraMap R p.ResidueField (e x) := sorry

/-- If a fiber coordinate of `x` is prescribed through a
`p.ResidueField`-algebra equivalence, then it is the residue class of its image under
`A ≃ₐ[R] R`. -/
theorem residueField_eq_of_tensor_eq
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {p : Ideal R} [p.IsPrime]
    (e : A ≃ₐ[R] R)
    (eκ : (p.ResidueField ⊗[R] A) ≃ₐ[p.ResidueField] p.ResidueField)
    {x : A} {a : p.ResidueField}
    (h : eκ (1 ⊗ₜ[R] x) = a) :
    algebraMap R p.ResidueField (e x) = a := sorry

/-- At the closed point of a local ring, a prescribed tensor-fiber coordinate of `x` is the
residue of its image under an `R`-algebra equivalence to `R`. -/
theorem residue_eq_of_tensor_eq
    {R : Type u} {A : Type v} [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A]
    (e : A ≃ₐ[R] R)
    (eκ : (ResidueField R ⊗[R] A) ≃ₐ[ResidueField R] ResidueField R)
    {x : A} {a : ResidueField R}
    (h : eκ (1 ⊗ₜ[R] x) = a) :
    residue R (e x) = a := sorry

end AlgEquiv

namespace AlgHom

universe u v

/-- An `R`-algebra retraction `τ : A →ₐ[R] R` induces a bijection on residue
fields at a prime `p` of `R` and its pullback `q` along `τ`. This specializes
`RingHom.SurjectiveOnStalks.residueFieldMap_bijective` using the retraction's
surjectivity. -/
theorem residueFieldMap_bijective_of_retraction
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (τ : A →ₐ[R] R) (q : Ideal A) [q.IsPrime] (p : Ideal R) [p.IsPrime]
    (hqp : q = Ideal.comap τ.toRingHom p) :
    Function.Bijective (Ideal.ResidueField.map q p τ.toRingHom hqp) := sorry

end AlgHom
