/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.TensorProduct.LocalTarget
public import ReasLib.RingTheory.LocalRing.Localization
public import ReasLib.RingTheory.RingHom.Local.Map

/-!
# Prime-localization maps into a local target

This leaf owns the canonical composite `S → Localization.AtPrime q → T` when a prime `q` of an
`R`-algebra `S` lies over `p`, together with the resulting tensor-local-target
construction.  It is independent of henselizations.  Its relative-algebra
form records the precise scalar-tower compatibility required to use the map
over `R`.

@stack 08HU
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace Localization.AtPrime.LocalTarget

section RingMap

variable {S : Type v} {T : Type w}
variable [CommSemiring S] [Semiring T]
variable (q : Ideal S) [q.IsPrime]
variable [Algebra (Localization.AtPrime q) T]

/-- The canonical ring map `S → Localization.AtPrime q → T` into a
target equipped with a `Localization.AtPrime q`-algebra structure. -/
@[stacks 08HU "source map through a prime localization"]
noncomputable def sourceMapRingHom : S →+* T :=
  (algebraMap (Localization.AtPrime q) T).comp (algebraMap S (Localization.AtPrime q))

end RingMap

section LocalRingMap

variable {S : Type v} {T : Type w}
variable [CommSemiring S] [CommSemiring T] [IsLocalRing T]
variable (q : Ideal S) [q.IsPrime]
variable [Algebra (Localization.AtPrime q) T]
variable [hLocalTarget : IsLocalHom (algebraMap (Localization.AtPrime q) T)]

include hLocalTarget in
/-- The canonical map `S → Localization.AtPrime q → T` contracts the maximal ideal of
the local target to `q`. -/
@[stacks 08HU "contraction of the prime-localized source map"]
theorem sourceMapRingHom.comap_maximalIdeal :
    Ideal.comap (sourceMapRingHom (q := q)) (IsLocalRing.maximalIdeal T) = q := sorry

end LocalRingMap

section RelativeAlgebra

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommSemiring R] [CommSemiring S] [Semiring T]
variable [Algebra R S] [Algebra R T]
variable (p : Ideal R) [p.IsPrime]
variable (q : Ideal S) [q.IsPrime] [hLiesOver : q.LiesOver p]
variable [Algebra (Localization.AtPrime p) T]
variable [Algebra (Localization.AtPrime q) T]
variable [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
variable [hAtPrimeAlgebra : Localization.AtPrime.IsLiesOverAlgebra p q]
variable [hTowerRT : IsScalarTower R (Localization.AtPrime p) T]
variable [hTowerRpSqT :
  IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q) T]

include hLiesOver hAtPrimeAlgebra in
/-- On elements of `R`, `sourceMapRingHom` agrees with the named
relative localization map encoded by
`Localization.AtPrime.IsLiesOverAlgebra p q`. -/
@[stacks 08HU "source map compatibility with relative localization"]
theorem sourceMapRingHom.map_algebraMap (r : R) :
    sourceMapRingHom (q := q) ((algebraMap R S) r) =
      (algebraMap (Localization.AtPrime q) T)
        ((algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
          ((algebraMap R (Localization.AtPrime p)) r)) := sorry

include hLiesOver hAtPrimeAlgebra hTowerRT hTowerRpSqT in
/-- The canonical source ring map is compatible with the specified
`R`-algebra structure on the target. -/
@[stacks 08HU "source map commutes with base scalars"]
theorem sourceMapRingHom.commutes (r : R) :
    sourceMapRingHom (q := q) ((algebraMap R S) r) = algebraMap R T r := sorry

include hLiesOver hAtPrimeAlgebra hTowerRT hTowerRpSqT in
/-- The canonical map `S → Localization.AtPrime q → T`, presented as an `R`-algebra
map using the specified compatible prime-localization scalar towers. -/
@[stacks 08HU "relative source algebra map"]
noncomputable def sourceMap : S →ₐ[R] T where
  toRingHom := sourceMapRingHom (q := q)
  commutes' := sourceMapRingHom.commutes (p := p) (q := q)

end RelativeAlgebra

section RelativeLocalAlgebra

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommSemiring R] [CommSemiring S] [CommSemiring T]
variable [Algebra R S] [Algebra R T]
variable (p : Ideal R) [p.IsPrime]
variable (q : Ideal S) [q.IsPrime] [hLiesOver : q.LiesOver p]
variable [Algebra (Localization.AtPrime p) T]
variable [Algebra (Localization.AtPrime q) T]
variable [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
variable [hAtPrimeAlgebra : Localization.AtPrime.IsLiesOverAlgebra p q]
variable [hTowerRT : IsScalarTower R (Localization.AtPrime p) T]
variable [hTowerRpSqT :
  IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q) T]
variable [IsLocalRing T]
variable [hLocalTarget : IsLocalHom (algebraMap (Localization.AtPrime q) T)]

include hLiesOver hAtPrimeAlgebra hTowerRT hTowerRpSqT hLocalTarget in
/-- The relative `R`-algebra source map contracts the maximal ideal
of its local target to `q`. -/
@[stacks 08HU "contraction of the relative source algebra map"]
theorem sourceMap_comap_maximalIdeal :
    Ideal.comap (sourceMap (p := p) (q := q)).toRingHom
      (IsLocalRing.maximalIdeal T) = q := sorry

end RelativeLocalAlgebra

section TensorMap

variable {R : Type u} {S : Type v} {A : Type w} {T : Type x}
variable [CommSemiring R] [CommSemiring S] [Semiring A] [CommSemiring T]
variable [Algebra R S] [Algebra R A] [Algebra R T]
variable (p : Ideal R) [p.IsPrime]
variable (q : Ideal S) [q.IsPrime] [hLiesOver : q.LiesOver p]
variable [Algebra (Localization.AtPrime p) A]
variable [Algebra (Localization.AtPrime p) T]
variable [Algebra (Localization.AtPrime q) T]
variable [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
variable [hAtPrimeAlgebra : Localization.AtPrime.IsLiesOverAlgebra p q]
variable [hTowerRA : IsScalarTower R (Localization.AtPrime p) A]
variable [hTowerRT : IsScalarTower R (Localization.AtPrime p) T]
variable [hTowerRpSqT :
  IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q) T]

include hLiesOver hAtPrimeAlgebra hTowerRA hTowerRT hTowerRpSqT in
/-- The tensor-product map `A ⊗[R] S → T` determined by an explicit
local comparison `A → T` over `Localization.AtPrime p` and the canonical source map
`S → Localization.AtPrime q → T`.
It is the at-prime specialization of Mathlib's
`Algebra.TensorProduct.productMap`. -/
@[stacks 08HU "at-prime tensor map into a local target"]
noncomputable def tensorMap
    (comparison : AlgHom.Local
      (R := Localization.AtPrime p) (A := A) (B := T)) : A ⊗[R] S →ₐ[R] T :=
  Algebra.TensorProduct.productMap
    (comparison.restrictScalars (R := R)).hom
    (sourceMap (p := p) (q := q))

include hLiesOver hAtPrimeAlgebra hTowerRA hTowerRT hTowerRpSqT in
/-- The at-prime tensor map restricts on the left factor to the
given explicit local comparison, after restriction of scalars to `R`. -/
@[simp, stacks 08HU "left restriction of the at-prime tensor map"]
theorem tensorMap_comp_includeLeft
    (comparison : AlgHom.Local
      (R := Localization.AtPrime p) (A := A) (B := T)) :
    (tensorMap (p := p) (q := q) comparison).comp
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] S) =
      (comparison.restrictScalars (R := R)).hom := sorry

include hLiesOver hAtPrimeAlgebra hTowerRA hTowerRT hTowerRpSqT in
/-- The at-prime tensor map restricts on the right factor to the
canonical source map `S → Localization.AtPrime q → T`. -/
@[simp, stacks 08HU "right restriction of the at-prime tensor map"]
theorem tensorMap_comp_includeRight
    (comparison : AlgHom.Local
      (R := Localization.AtPrime p) (A := A) (B := T)) :
    (tensorMap (p := p) (q := q) comparison).comp
        (Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S) =
      sourceMap (p := p) (q := q) := sorry

end TensorMap

section TensorLocal

variable {R : Type u} {S : Type v} {A : Type w} {T : Type x}
variable [CommSemiring R] [CommSemiring S] [CommSemiring A] [CommSemiring T]
variable [Algebra R S] [Algebra R A] [Algebra R T]
variable (p : Ideal R) [p.IsPrime]
variable (q : Ideal S) [q.IsPrime] [hLiesOver : q.LiesOver p]
variable [Algebra (Localization.AtPrime p) A]
variable [Algebra (Localization.AtPrime p) T]
variable [Algebra (Localization.AtPrime q) T]
variable [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
variable [hAtPrimeAlgebra : Localization.AtPrime.IsLiesOverAlgebra p q]
variable [hTowerRA : IsScalarTower R (Localization.AtPrime p) A]
variable [hTowerRT : IsScalarTower R (Localization.AtPrime p) T]
variable [hTowerRpSqT :
  IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q) T]

variable [IsLocalRing T]

include hLiesOver hAtPrimeAlgebra hTowerRA hTowerRT hTowerRpSqT in
/-- The prime of `A ⊗[R] S` cut out by the closed point of `T`
under the explicit at-prime comparison. -/
@[stacks 08HU "at-prime tensor prime from a local comparison"]
noncomputable def tensorPrime
    (comparison : AlgHom.Local
      (R := Localization.AtPrime p) (A := A) (B := T)) : PrimeSpectrum (A ⊗[R] S) :=
  Algebra.TensorProduct.LocalTarget.tensorPrime
    (comparison.restrictScalars (R := R)).hom
    (sourceMap (p := p) (q := q))

include hLiesOver hAtPrimeAlgebra hTowerRA hTowerRT hTowerRpSqT in
/-- The map from the localization of `A ⊗[R] S` at `tensorPrime`
to `T`.  The local target supplies its canonical self-localization internally. -/
@[stacks 08HU "localized at-prime tensor map"]
noncomputable def localizedMap
    (comparison : AlgHom.Local
      (R := Localization.AtPrime p) (A := A) (B := T)) :
    Localization.AtPrime
      (tensorPrime (p := p) (q := q) comparison).asIdeal →+* T :=
  Algebra.TensorProduct.LocalTarget.localizedMap
    (comparison.restrictScalars (R := R)).hom
    (sourceMap (p := p) (q := q))

include hLiesOver hAtPrimeAlgebra hTowerRA hTowerRT hTowerRpSqT in
/-- The explicitly named algebra structure on `T` over the
localization of the at-prime tensor product.  It is not a global instance,
because it depends on the explicit comparison into the local target. -/
@[reducible, stacks 08HU "localized algebra for an at-prime tensor target"]
noncomputable def localizedAlgebra
    (comparison : AlgHom.Local
      (R := Localization.AtPrime p) (A := A) (B := T)) :
    Algebra (Localization.AtPrime
      (tensorPrime (p := p) (q := q) comparison).asIdeal) T :=
  Algebra.TensorProduct.LocalTarget.localizedAlgebra
    (comparison.restrictScalars (R := R)).hom
    (sourceMap (p := p) (q := q))

include hLiesOver hAtPrimeAlgebra hTowerRA hTowerRT hTowerRpSqT in
/-- The tensor prime contracts along the left tensor inclusion to
the maximal ideal of its left local factor. -/
@[stacks 08HU "left contraction of the at-prime tensor prime"]
theorem tensorPrime_comap_includeLeft
    (comparison : AlgHom.Local
      (R := Localization.AtPrime p) (A := A) (B := T))
    [IsLocalRing A] :
    Ideal.comap
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] S)
        (tensorPrime (p := p) (q := q) comparison).asIdeal =
      IsLocalRing.maximalIdeal A := sorry

section RightContraction

variable [hLocalTarget : IsLocalHom (algebraMap (Localization.AtPrime q) T)]

include hLiesOver hAtPrimeAlgebra hTowerRA hTowerRT hTowerRpSqT hLocalTarget in
/-- The tensor prime contracts along the right tensor inclusion to
the selected prime `q` of `S`. -/
@[stacks 08HU "right contraction of the at-prime tensor prime"]
theorem tensorPrime_comap_includeRight
    (comparison : AlgHom.Local
      (R := Localization.AtPrime p) (A := A) (B := T)) :
    Ideal.comap
        (Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S).toRingHom
        (tensorPrime (p := p) (q := q) comparison).asIdeal =
      q := sorry

end RightContraction

include hLiesOver hAtPrimeAlgebra hTowerRA hTowerRT hTowerRpSqT in
/-- `localizedMap` agrees with the unlocalized at-prime tensor map
on elements of `A ⊗[R] S`. -/
@[stacks 08HU "localized at-prime tensor map extension"]
theorem localizedMap_algebraMap
    (comparison : AlgHom.Local
      (R := Localization.AtPrime p) (A := A) (B := T))
    (x : A ⊗[R] S) :
    localizedMap (p := p) (q := q) comparison
        (algebraMap (A ⊗[R] S)
          (Localization.AtPrime
            (tensorPrime (p := p) (q := q) comparison).asIdeal) x) =
      tensorMap (p := p) (q := q) comparison x := sorry

include hLiesOver hAtPrimeAlgebra hTowerRA hTowerRT hTowerRpSqT in
/-- After localizing at the tensor prime, the map to `T` restricts
on the left to the explicit comparison map. -/
@[stacks 08HU "left restriction after at-prime localization"]
theorem localizedMap_comp_includeLeft
    (comparison : AlgHom.Local
      (R := Localization.AtPrime p) (A := A) (B := T)) :
    (localizedMap (p := p) (q := q) comparison).comp
        ((algebraMap (A ⊗[R] S)
            (Localization.AtPrime
              (tensorPrime (p := p) (q := q) comparison).asIdeal)).comp
          (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] S)) =
      (comparison.restrictScalars (R := R)).hom.toRingHom := sorry

include hLiesOver hAtPrimeAlgebra hTowerRA hTowerRT hTowerRpSqT in
/-- After localizing at the tensor prime, the map to `T` restricts
on the right to the canonical source map. -/
@[stacks 08HU "right restriction after at-prime localization"]
theorem localizedMap_comp_includeRight
    (comparison : AlgHom.Local
      (R := Localization.AtPrime p) (A := A) (B := T)) :
    (localizedMap (p := p) (q := q) comparison).comp
        ((algebraMap (A ⊗[R] S)
            (Localization.AtPrime
              (tensorPrime (p := p) (q := q) comparison).asIdeal)).comp
          (Algebra.TensorProduct.includeRight : S →ₐ[R] A ⊗[R] S).toRingHom) =
      (sourceMap (p := p) (q := q)).toRingHom := sorry

include hLiesOver hAtPrimeAlgebra hTowerRA hTowerRT hTowerRpSqT in
/-- The localized at-prime tensor map is local. -/
@[stacks 08HU "locality of the at-prime localized tensor map"]
theorem localizedMap_isLocalHom
    (comparison : AlgHom.Local
      (R := Localization.AtPrime p) (A := A) (B := T)) :
    IsLocalHom (localizedMap (p := p) (q := q) comparison) := sorry

end TensorLocal

end Localization.AtPrime.LocalTarget
