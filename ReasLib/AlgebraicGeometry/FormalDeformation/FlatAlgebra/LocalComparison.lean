module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.Product
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.Localization
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.Henselization.Smooth
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.HenselCompletion
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Local comparison maps of algebra deformation categories

Localization, henselization, and completion induce canonical functors between
families of algebra deformations sharing one Artinian local base.
-/

@[expose] public section

open CategoryTheory Functor IsLocalRing RingPairCat
open scoped BasedFunctor

universe u

noncomputable section

namespace FlatAlgebraCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {P : Type u} [CommRing P] [Algebra k P]
variable {ι : Type u}

/-- The local ring `P_{m i}` at a maximal ideal. -/
abbrev localRing (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (i : ι) : Type u :=
  Localization.AtPrime (m i)

variable (Λ k) in
/-- Localization at each maximal ideal, as a based functor into the product of
the local deformation categories. -/
def localizationPiBasedFunctor (m : ι → Ideal P) [∀ i, (m i).IsMaximal] :
    BasedCategory.ofFunctor (deformationForget Λ k P) ⥤ᵇ
      BasedCategory.ofFunctor (deformationPiForget Λ k (localRing m)) :=
  pairing Λ k (localRing m) (deformationForget Λ k P) fun i ↦
    localizationBasedFunctor Λ k (m i).primeCompl

variable (Λ k) in
/-- The underlying functor of `localizationPiBasedFunctor` retains the Artinian base. -/
theorem localizationPiBasedFunctor_obj_base (m : ι → Ideal P) [∀ i, (m i).IsMaximal]
    (ξ : deformationCategory Λ k P) :
    ((localizationPiBasedFunctor Λ k m).toFunctor.obj ξ).1 =
      (deformationForget Λ k P).obj ξ :=
  rfl

variable (Λ k) in
/-- The `i`-th factor of `localizationPiBasedFunctor` is localization at
`(m i).primeCompl`. -/
theorem localizationPiBasedFunctor_toFunctor (m : ι → Ideal P) [∀ i, (m i).IsMaximal]
    (ξ : deformationCategory Λ k P) (i : ι) :
    (evalBasedFunctor Λ k (localRing m) i).toFunctor.obj
        ((localizationPiBasedFunctor Λ k m).toFunctor.obj ξ) =
      (localizationBasedFunctor Λ k (m i).primeCompl).toFunctor.obj ξ :=
  rfl

variable [henselianPairInclusion.IsRightAdjoint]

/-- The henselization `P_{m i}^h` of the local ring at `m i`. -/
abbrev henselRing (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (i : ι) : Type u :=
  henselizationRing (pairOfIdeal (maximalIdeal (localRing m i)))

variable (Λ k) in
/-- Pair henselization of each local ring, as a based functor of deformation
products. -/
def henselizationPiBasedFunctor (m : ι → Ideal P) [∀ i, (m i).IsMaximal] :
    BasedCategory.ofFunctor (deformationPiForget Λ k (localRing m)) ⥤ᵇ
      BasedCategory.ofFunctor (deformationPiForget Λ k (henselRing m)) :=
  deformationPiMap Λ k (localRing m) (henselRing m) fun i ↦
    henselizationBasedFunctor Λ k (localRing m i) (maximalIdeal (localRing m i))

variable (Λ k) in
/-- The underlying functor of `henselizationPiBasedFunctor` retains the Artinian base. -/
theorem henselizationPiBasedFunctor_obj_base (m : ι → Ideal P) [∀ i, (m i).IsMaximal]
    (X : deformationPi Λ k (localRing m)) :
    ((henselizationPiBasedFunctor Λ k m).toFunctor.obj X).1 = X.1 :=
  rfl

variable (Λ k) in
/-- The `i`-th factor of `henselizationPiBasedFunctor` is pair henselization of
`localRing m i` along its maximal ideal. -/
theorem henselizationPiBasedFunctor_toFunctor (m : ι → Ideal P) [∀ i, (m i).IsMaximal]
    (X : deformationPi Λ k (localRing m)) (i : ι) :
    (evalBasedFunctor Λ k (henselRing m) i).toFunctor.obj
        ((henselizationPiBasedFunctor Λ k m).toFunctor.obj X) =
      (henselizationBasedFunctor Λ k (localRing m i)
          (maximalIdeal (localRing m i))).toFunctor.obj
        (Fiber.fiberInclusion.obj (X.2 i)) :=
  rfl

/-- The completion `P_{m i}^∧` of the local ring at `m i`. -/
abbrev completeRing (m : ι → Ideal P) [∀ i, (m i).IsMaximal] (i : ι) : Type u :=
  AdicCompletion (maximalIdeal (localRing m i)) (localRing m i)

variable (Λ k) in
/-- Adic completion of each henselian local ring, as a based functor of
deformation products landing in `∏ Def_{P_{m i}^∧}`. -/
def completionPiBasedFunctor [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal] :
    BasedCategory.ofFunctor (deformationPiForget Λ k (henselRing m)) ⥤ᵇ
      BasedCategory.ofFunctor (deformationPiForget Λ k (completeRing m)) :=
  -- Local instance justification (proof-local temporary data): finite type over k supplies the canonical Prop-valued Noetherianness proof for P and its localizations; k is not inferable from IsNoetherianRing P, so no coherent global instance can supply it.
  letI := Algebra.FiniteType.isNoetherianRing k P
  deformationPiMap Λ k (henselRing m) (completeRing m) fun i ↦
    completionFromHenselLocalBasedFunctor Λ k (localRing m i)

variable (Λ k) in
/-- The underlying functor of `completionPiBasedFunctor` retains the Artinian base. -/
theorem completionPiBasedFunctor_obj_base [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal]
    (X : deformationPi Λ k (henselRing m)) :
    ((completionPiBasedFunctor Λ k m).toFunctor.obj X).1 = X.1 :=
  rfl

variable (Λ k) in
/-- Each factor of the completion comparison is the canonical local completion functor. -/
theorem completionPiBasedFunctor_toFunctor [Algebra.FiniteType k P]
    (m : ι → Ideal P) [∀ i, (m i).IsMaximal]
    (X : deformationPi Λ k (henselRing m)) (i : ι) :
    let : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
    (evalBasedFunctor Λ k (completeRing m) i).toFunctor.obj
        ((completionPiBasedFunctor Λ k m).toFunctor.obj X) =
      (completionFromHenselLocalBasedFunctor Λ k (localRing m i)).toFunctor.obj
        (Fiber.fiberInclusion.obj (X.2 i)) := rfl

end FlatAlgebraCat

end
