/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.MvPolynomial.Counit
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Augmentation.Homology
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.BaseChange.Homology.Descent
public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.Transport
public import ReasLib.RingTheory.DividedPowers.Tate.Tor.BaseChange.RestrictScalars

/-!
# Divided powers on Tor from a Tate model

An explicit Tate resolution of the second algebra, a flat coefficient cover of the first
algebra, and supplied base-change models determine divided powers on the restricted model
homology.  Transport through the canonical degreewise homology--Tor equivalence puts the full
strictly graded-commutative algebra and divided-power structure on Mathlib's `Tor` objects.

The construction is explicit non-Prop data.  Separate theorems state independence of the
coefficient cover, the supplied base-change models, and the Tate resolution.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v x

namespace TateResolution.Tor

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

/-- The canonical degree-`n` Mathlib Tor module for the two `R`-algebras `S` and `T`. -/
@[stacks 09PQ "canonical Tor module underlying the Tate comparison"]
abbrev object (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (n : ℕ) : ModuleCat R :=
  ((CategoryTheory.Tor (ModuleCat R) n).obj (ModuleCat.of R S)).obj
    (ModuleCat.of R T)

variable {J : Type v} {pi0 : MvPolynomial J R →ₐ[R] T}

/-- The chain DGA underlying a Tate resolution has vanishing positive homology, as its
augmentation is a quasi-isomorphism to an algebra concentrated in degree zero. -/
@[stacks 09PQ "positive acyclicity of a Tate resolution"]
theorem positiveHomologyVanishes (A : TateResolution.{u, v} pi0) :
    A.algebra.toChainDGAlgebra.PositiveHomologyVanishes := sorry

section Construction

variable {P : Type u} [CommRing P] [Algebra R P]

/-- The explicit strictly graded-commutative divided-power algebra on the canonical Tor modules
obtained from a supplied Tate resolution, coefficient cover, and scalar-extension models. -/
@[stacks 09PQ "model construction of divided powers on Tor"]
noncomputable def algebraOfModel
    (A : TateResolution.{u, v} pi0)
    (X : DividedPowerChainAlgebra.BaseChange (R' := P) A.algebra)
    (sigma : P →ₐ[R] S)
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra)
    (h_flat : (algebraMap R P).Flat) (h_sigma : Function.Surjective sigma) :
    DividedPowerGradedAlgebra R :=
  DividedPowerGradedAlgebra.transport
    (DividedPowerChainAlgebra.BaseChange.Descent.homologyDPAlgebra
      X sigma Y h_flat (positiveHomologyVanishes A) h_sigma)
    (TateResolution.BaseChange.homologyTorEquiv A Y)

/-- The canonical divided-power isomorphism from restricted model homology to the transported
Tor algebra. -/
@[stacks 09PQ "transport from Tate homology to the Tor algebra"]
def transportIso
    (A : TateResolution.{u, v} pi0)
    (X : DividedPowerChainAlgebra.BaseChange (R' := P) A.algebra)
    (sigma : P →ₐ[R] S)
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra)
    (h_flat : (algebraMap R P).Flat) (h_sigma : Function.Surjective sigma) :
    DividedPowerChainAlgebra.BaseChange.Descent.homologyDPAlgebra
        X sigma Y h_flat (positiveHomologyVanishes A) h_sigma ≅
      algebraOfModel A X sigma Y h_flat h_sigma :=
  DividedPowerGradedAlgebra.transportIso
    (DividedPowerChainAlgebra.BaseChange.Descent.homologyDPAlgebra
      X sigma Y h_flat (positiveHomologyVanishes A) h_sigma)
    (TateResolution.BaseChange.homologyTorEquiv A Y)

/-- The homogeneous map from restricted model homology into the Tor algebra is the canonical
homology--Tor equivalence. -/
@[stacks 09PQ "homogeneous transport map for Tor divided powers", simp]
theorem transportIso_hom_map
    (A : TateResolution.{u, v} pi0)
    (X : DividedPowerChainAlgebra.BaseChange (R' := P) A.algebra)
    (sigma : P →ₐ[R] S)
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra)
    (h_flat : (algebraMap R P).Flat) (h_sigma : Function.Surjective sigma)
    (n : ℕ) :
    (transportIso A X sigma Y h_flat h_sigma).hom.toGradedHom.map n =
      (TateResolution.BaseChange.homologyTorEquiv A Y n).toLinearMap := sorry

/-- The degree-`n` carrier of the model construction is the canonical Mathlib Tor module. -/
@[stacks 09PQ "model degree pieces are canonical Tor modules"]
theorem algebraOfModel_piece
    (A : TateResolution.{u, v} pi0)
    (X : DividedPowerChainAlgebra.BaseChange (R' := P) A.algebra)
    (sigma : P →ₐ[R] S)
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra)
    (h_flat : (algebraMap R P).Flat) (h_sigma : Function.Surjective sigma)
    (n : ℕ) :
    (algebraOfModel A X sigma Y h_flat h_sigma).toGradedAlgebra.piece n =
      object R S T n := sorry

/-- The unit on Tor is the transport of the unit in restricted model homology. -/
@[stacks 09PQ "unit transport for model Tor divided powers", simp]
theorem algebraOfModel_one
    (A : TateResolution.{u, v} pi0)
    (X : DividedPowerChainAlgebra.BaseChange (R' := P) A.algebra)
    (sigma : P →ₐ[R] S)
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra)
    (h_flat : (algebraMap R P).Flat) (h_sigma : Function.Surjective sigma) :
    (algebraOfModel A X sigma Y h_flat h_sigma).toGradedAlgebra.one =
      TateResolution.BaseChange.homologyTorEquiv A Y 0
        ((DividedPowerChainAlgebra.BaseChange.Descent.homologyDPAlgebra
          X sigma Y h_flat (positiveHomologyVanishes A) h_sigma).toGradedAlgebra.one) := sorry

/-- Multiplication on Tor is the transport of multiplication in restricted model homology. -/
@[stacks 09PQ "multiplication transport for model Tor divided powers", simp]
theorem algebraOfModel_mul
    (A : TateResolution.{u, v} pi0)
    (X : DividedPowerChainAlgebra.BaseChange (R' := P) A.algebra)
    (sigma : P →ₐ[R] S)
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra)
    (h_flat : (algebraMap R P).Flat) (h_sigma : Function.Surjective sigma)
    (m n : ℕ)
    (x : (TateResolution.BaseChange.restrictedAlgebra A Y).toChainDGAlgebra.homologyPiece m)
    (y : (TateResolution.BaseChange.restrictedAlgebra A Y).toChainDGAlgebra.homologyPiece n) :
    (algebraOfModel A X sigma Y h_flat h_sigma).toGradedAlgebra.mul
        (TateResolution.BaseChange.homologyTorEquiv A Y m x :
          (algebraOfModel A X sigma Y h_flat h_sigma).toGradedAlgebra.piece m)
        (TateResolution.BaseChange.homologyTorEquiv A Y n y :
          (algebraOfModel A X sigma Y h_flat h_sigma).toGradedAlgebra.piece n) =
      TateResolution.BaseChange.homologyTorEquiv A Y (m + n)
        ((DividedPowerChainAlgebra.BaseChange.Descent.homologyDPAlgebra
          X sigma Y h_flat (positiveHomologyVanishes A) h_sigma).toGradedAlgebra.mul x y) := sorry

/-- Divided powers on a transported homogeneous class are transported from the intrinsic
divided powers on restricted base-change homology. -/
@[stacks 09PQ "divided-power transport for model Tor classes", simp]
theorem algebraOfModel_gammaPiece
    (A : TateResolution.{u, v} pi0)
    (X : DividedPowerChainAlgebra.BaseChange (R' := P) A.algebra)
    (sigma : P →ₐ[R] S)
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra)
    (h_flat : (algebraMap R P).Flat) (h_sigma : Function.Surjective sigma)
    (n d : ℕ)
    (x : (TateResolution.BaseChange.restrictedAlgebra A Y).toChainDGAlgebra.homologyPiece
      (2 * (d + 1))) :
    (algebraOfModel A X sigma Y h_flat h_sigma).gamma.gammaPiece n d
        (TateResolution.BaseChange.homologyTorEquiv A Y (2 * (d + 1)) x) =
      TateResolution.BaseChange.homologyTorEquiv A Y (2 * (n * (d + 1)))
        ((DividedPowerChainAlgebra.BaseChange.Descent.homologyDPAlgebra
          X sigma Y h_flat (positiveHomologyVanishes A) h_sigma).gamma.gammaPiece n d x) := sorry

end Construction

section Independence

variable {P Q : Type u} [CommRing P] [CommRing Q] [Algebra R P] [Algebra R Q]

/-- Tag 09PQ: the Tor divided-power algebra is independent of the flat surjective coefficient
cover used with a fixed Tate resolution and target base-change model. -/
@[stacks 09PQ "independence of the coefficient cover for Tor divided powers"]
theorem algebraOfModel_eq_of_covers
    (A : TateResolution.{u, v} pi0)
    (X : DividedPowerChainAlgebra.BaseChange (R' := P) A.algebra) (sigma : P →ₐ[R] S)
    (Z : DividedPowerChainAlgebra.BaseChange (R' := Q) A.algebra) (tau : Q →ₐ[R] S)
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra)
    (hP : (algebraMap R P).Flat) (hQ : (algebraMap R Q).Flat)
    (h_sigma : Function.Surjective sigma) (h_tau : Function.Surjective tau) :
    algebraOfModel A X sigma Y hP h_sigma =
      algebraOfModel A Z tau Y hQ h_tau := sorry

/-- Tag 09PQ: for a fixed Tate resolution and coefficient cover, the transported Tor algebra is
independent of all supplied scalar-extension models. -/
@[stacks 09PQ "independence of base-change models for Tor divided powers"]
theorem algebraOfModel_eq_of_models
    (A : TateResolution.{u, v} pi0) (sigma : P →ₐ[R] S)
    (X X' : DividedPowerChainAlgebra.BaseChange (R' := P) A.algebra)
    (Y Y' : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra)
    (hP : (algebraMap R P).Flat) (h_sigma : Function.Surjective sigma) :
    algebraOfModel A X sigma Y hP h_sigma =
      algebraOfModel A X' sigma Y' hP h_sigma := sorry

variable {K : Type x} {pi0' : MvPolynomial K R →ₐ[R] T}

/-- Lemma 23.6.12 (Tag 09PQ), canonicality: constructions from arbitrary supplied Tate
resolutions, flat coefficient covers, and base-change models give the same divided-power algebra
on the fixed Mathlib Tor objects. -/
@[stacks 09PQ "independence of the Tate construction on Tor"]
theorem algebraOfModel_eq_of_resolutions
    (A : TateResolution.{u, v} pi0) (B : TateResolution.{u, x} pi0')
    (X : DividedPowerChainAlgebra.BaseChange (R' := P) A.algebra) (sigma : P →ₐ[R] S)
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra)
    (Z : DividedPowerChainAlgebra.BaseChange (R' := Q) B.algebra) (tau : Q →ₐ[R] S)
    (W : DividedPowerChainAlgebra.BaseChange (R' := S) B.algebra)
    (hP : (algebraMap R P).Flat) (hQ : (algebraMap R Q).Flat)
    (h_sigma : Function.Surjective sigma) (h_tau : Function.Surjective tau) :
    algebraOfModel A X sigma Y hP h_sigma =
      algebraOfModel B Z tau W hQ h_tau := sorry

end Independence

namespace Polynomial

/-- The canonical polynomial coefficient cover used to construct Tor divided powers. -/
@[stacks 09PQ "polynomial coefficient cover for Tor divided powers"]
abbrev cover (R S : Type u) [CommRing R] [CommRing S] : Type u :=
  MvPolynomial S R

/-- The canonical polynomial cover maps the variable indexed by `s : S` to `s`. -/
@[stacks 09PQ "polynomial coefficient cover map for Tor divided powers"]
noncomputable def coverMap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    cover R S →ₐ[R] S :=
  MvPolynomial.ACounit R S

/-- The canonical polynomial coefficient cover is surjective. -/
@[stacks 09PQ "surjectivity of the polynomial coefficient cover"]
theorem coverMap_surjective (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    Function.Surjective (coverMap R S) := sorry

/-- The canonical polynomial coefficient cover is flat over its coefficient ring. -/
@[stacks 09PQ "flatness of the polynomial coefficient cover"]
theorem cover_flat (R S : Type u) [CommRing R] [CommRing S] :
    (algebraMap R (cover R S)).Flat := sorry

/-- Tag 09PQ: the divided-power Tor algebra obtained from the canonical polynomial presentations
of the two input algebras and supplied Tate/base-change realizations. -/
@[stacks 09PQ "polynomial-model divided-power algebra on Tor"]
noncomputable def algebra
    (A : TateResolution (MvPolynomial.ACounit R T))
    (X : DividedPowerChainAlgebra.BaseChange (R' := cover R S) A.algebra)
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) :
    DividedPowerGradedAlgebra R :=
  algebraOfModel A X (coverMap R S) Y (cover_flat R S) (coverMap_surjective R S)

/-- The degree-`n` carrier of the polynomial-model algebra is the canonical Mathlib Tor module. -/
@[stacks 09PQ "polynomial-model degree pieces are canonical Tor modules"]
theorem algebra_piece
    (A : TateResolution (MvPolynomial.ACounit R T))
    (X : DividedPowerChainAlgebra.BaseChange (R' := cover R S) A.algebra)
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) (n : ℕ) :
    (algebra A X Y).toGradedAlgebra.piece n = object R S T n := sorry

/-- The polynomial-model unit is transported from restricted Tate homology. -/
@[stacks 09PQ "unit of the polynomial-model Tor algebra", simp]
theorem algebra_one
    (A : TateResolution (MvPolynomial.ACounit R T))
    (X : DividedPowerChainAlgebra.BaseChange (R' := cover R S) A.algebra)
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) :
    (algebra A X Y).toGradedAlgebra.one =
      TateResolution.BaseChange.homologyTorEquiv A Y 0
        ((DividedPowerChainAlgebra.BaseChange.Descent.homologyDPAlgebra
          X (coverMap R S) Y (cover_flat R S) (positiveHomologyVanishes A)
            (coverMap_surjective R S)).toGradedAlgebra.one) := sorry

/-- Polynomial-model multiplication is transported from restricted Tate homology. -/
@[stacks 09PQ "multiplication of the polynomial-model Tor algebra", simp]
theorem algebra_mul
    (A : TateResolution (MvPolynomial.ACounit R T))
    (X : DividedPowerChainAlgebra.BaseChange (R' := cover R S) A.algebra)
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra)
    (m n : ℕ)
    (x : (TateResolution.BaseChange.restrictedAlgebra A Y).toChainDGAlgebra.homologyPiece m)
    (y : (TateResolution.BaseChange.restrictedAlgebra A Y).toChainDGAlgebra.homologyPiece n) :
    (algebra A X Y).toGradedAlgebra.mul
        (TateResolution.BaseChange.homologyTorEquiv A Y m x :
          (algebra A X Y).toGradedAlgebra.piece m)
        (TateResolution.BaseChange.homologyTorEquiv A Y n y :
          (algebra A X Y).toGradedAlgebra.piece n) =
      TateResolution.BaseChange.homologyTorEquiv A Y (m + n)
        ((DividedPowerChainAlgebra.BaseChange.Descent.homologyDPAlgebra
          X (coverMap R S) Y (cover_flat R S) (positiveHomologyVanishes A)
            (coverMap_surjective R S)).toGradedAlgebra.mul x y) := sorry

/-- Polynomial-model divided powers are transported from the intrinsic restricted-homology
divided powers. -/
@[stacks 09PQ "divided powers of the polynomial-model Tor algebra", simp]
theorem algebra_gammaPiece
    (A : TateResolution (MvPolynomial.ACounit R T))
    (X : DividedPowerChainAlgebra.BaseChange (R' := cover R S) A.algebra)
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra)
    (n d : ℕ)
    (x : (TateResolution.BaseChange.restrictedAlgebra A Y).toChainDGAlgebra.homologyPiece
      (2 * (d + 1))) :
    (algebra A X Y).gamma.gammaPiece n d
        (TateResolution.BaseChange.homologyTorEquiv A Y (2 * (d + 1)) x) =
      TateResolution.BaseChange.homologyTorEquiv A Y (2 * (n * (d + 1)))
        ((DividedPowerChainAlgebra.BaseChange.Descent.homologyDPAlgebra
          X (coverMap R S) Y (cover_flat R S) (positiveHomologyVanishes A)
            (coverMap_surjective R S)).gamma.gammaPiece n d x) := sorry

/-- For a fixed Tate resolution, the polynomial-model Tor algebra is independent of both supplied
base-change realizations. -/
@[stacks 09PQ "independence of polynomial base-change realizations"]
theorem algebra_eq_of_models
    (A : TateResolution (MvPolynomial.ACounit R T))
    (X X' : DividedPowerChainAlgebra.BaseChange (R' := cover R S) A.algebra)
    (Y Y' : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) :
    algebra A X Y = algebra A X' Y' := sorry

/-- Lemma 23.6.12 (Tag 09PQ), canonicality: polynomial-model constructions from arbitrary
supplied Tate resolutions and base-change realizations give the same Tor divided-power algebra. -/
@[stacks 09PQ "independence of polynomial models for Tor divided powers"]
theorem algebra_eq_of_resolutions
    (A B : TateResolution (MvPolynomial.ACounit R T))
    (X : DividedPowerChainAlgebra.BaseChange (R' := cover R S) A.algebra)
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra)
    (Z : DividedPowerChainAlgebra.BaseChange (R' := cover R S) B.algebra)
    (W : DividedPowerChainAlgebra.BaseChange (R' := S) B.algebra) :
    algebra A X Y = algebra B Z W := sorry

end Polynomial

/-- A divided-power graded algebra is the canonical one on `Tor_*^R(S, T)` when it agrees with
every explicit polynomial Tate model and every pair of scalar-extension models.  This universal
specification exposes direct rewrite API for arbitrary supplied models and stores no chosen
resolution. -/
@[stacks 09PQ "canonical divided-power structure on Tor"]
def IsCanonical (D : DividedPowerGradedAlgebra R) : Prop :=
  ∀ (A : TateResolution (MvPolynomial.ACounit R T))
    (X : DividedPowerChainAlgebra.BaseChange
      (R' := Polynomial.cover R S) A.algebra)
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra),
      D = Polynomial.algebra A X Y

namespace Polynomial

/-- Every explicit polynomial Tate/base-change model produces the canonical divided-power
structure on `Tor_*^R(S, T)`. -/
@[stacks 09PQ "explicit models produce the canonical Tor divided powers"]
theorem algebra_isCanonical
    (A : TateResolution (MvPolynomial.ACounit R T))
    (X : DividedPowerChainAlgebra.BaseChange
      (R' := cover R S) A.algebra)
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) :
    IsCanonical (S := S) (T := T) (algebra A X Y) := sorry

end Polynomial

namespace IsCanonical

/-- A canonical Tor divided-power algebra is equal to the algebra built from any supplied
polynomial Tate/base-change model. -/
@[stacks 09PQ "canonical Tor divided powers agree with every explicit model"]
theorem eq_model {D : DividedPowerGradedAlgebra R}
    (hD : IsCanonical (S := S) (T := T) D)
    (A : TateResolution (MvPolynomial.ACounit R T))
    (X : DividedPowerChainAlgebra.BaseChange
      (R' := Polynomial.cover R S) A.algebra)
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra) :
    D = Polynomial.algebra A X Y := sorry

/-- A canonical Tor divided-power algebra agrees with the construction from any supplied Tate
resolution and any flat-surjective coefficient cover. -/
@[stacks 09PQ "canonical Tor divided powers agree with arbitrary Tate models"]
theorem eq_algebraOfModel {D : DividedPowerGradedAlgebra R}
    (hD : IsCanonical (S := S) (T := T) D)
    {J : Type v} {pi0 : MvPolynomial J R →ₐ[R] T}
    {P : Type u} [CommRing P] [Algebra R P]
    (A : TateResolution.{u, v, u} pi0)
    (X : DividedPowerChainAlgebra.BaseChange (R' := P) A.algebra)
    (sigma : P →ₐ[R] S)
    (Y : DividedPowerChainAlgebra.BaseChange (R' := S) A.algebra)
    (h_flat : (algebraMap R P).Flat) (h_sigma : Function.Surjective sigma) :
    D = algebraOfModel A X sigma Y h_flat h_sigma := sorry

/-- Two canonical divided-power algebra structures on the same Mathlib Tor objects are equal. -/
@[stacks 09PQ "uniqueness of the canonical Tor divided powers"]
theorem eq {D E : DividedPowerGradedAlgebra R}
    (hD : IsCanonical (S := S) (T := T) D)
    (hE : IsCanonical (S := S) (T := T) E) : D = E := sorry

/-- Every homogeneous piece of a canonical Tor divided-power algebra is the corresponding
Mathlib Tor module. -/
@[stacks 09PQ "homogeneous pieces of the canonical Tor divided-power algebra"]
theorem piece {D : DividedPowerGradedAlgebra R}
    (hD : IsCanonical (S := S) (T := T) D) (n : ℕ) :
    D.toGradedAlgebra.piece n = object R S T n := sorry

end IsCanonical

/-- A canonical divided-power algebra structure exists on the Mathlib Tor objects. -/
@[stacks 09PQ "existence of canonical divided powers on Tor"]
theorem exists_isCanonical :
    ∃ D : DividedPowerGradedAlgebra R, IsCanonical (S := S) (T := T) D := sorry

/-- Lemma 23.6.12 (Tag 09PQ): the Mathlib Tor objects carry a unique divided-power graded-algebra
structure arising from a Tate resolution and scalar-extension models. -/
@[stacks 09PQ "unique canonical divided-power algebra on Tor"]
theorem existsUnique_isCanonical :
    ∃! D : DividedPowerGradedAlgebra R, IsCanonical (S := S) (T := T) D := sorry

end TateResolution.Tor
