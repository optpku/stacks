/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Smooth.Factorization.SmoothAt
public import ReasLib.RingTheory.Smooth.Resolution.Ideal

@[expose] public section

/-!
# Resolution of an algebra map at a prime

Resolution is owned by the algebra homomorphism whose transported singular
ideal is being improved.  This avoids rebuilding an ambient algebra structure
and scalar tower merely to name the map.
-/

universe u v w

namespace AlgHom

variable {R : Type u} {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ]

/-- A resolution at a target prime is a singular resolution along its
underlying prime ideal. -/
@[stacks 07F7 "resolution witness at a prime"]
abbrev ResolutionAtPrime (φ : A →ₐ[R] Λ) (q : PrimeSpectrum Λ) :=
  AlgHom.Factorisation.Finite.Resolution φ q.asIdeal

namespace ResolutionAtPrime

variable {φ : A →ₐ[R] Λ} {q : PrimeSpectrum Λ}

/-- The midpoint of a resolution is smooth at the prime pulled back from the
target point. -/
@[stacks 07F7 "smooth midpoint of a resolution at a prime"]
theorem smoothAt (W : ResolutionAtPrime φ q) :
    Algebra.SmoothAtPrime R W.mid
      (PrimeSpectrum.comap W.toTarget.toRingHom q) := sorry

/-- Forget the comparison with the original singular ideal and retain the
pointwise-smooth finite factorisation. -/
@[stacks 07F7 "resolution to pointwise-smooth factorisation"]
def toSmoothAt (W : ResolutionAtPrime φ q) :
    Factorisation.Finite.SmoothAt φ q :=
  Factorisation.Finite.SmoothAt.of W.factorisation W.smoothAt

/-- Promote a pointwise-smooth factorisation to a resolution once its
singular ideal contains that of the original map. -/
@[stacks 07F7 "pointwise-smooth factorisation to resolution"]
def ofSmoothAt (F : Factorisation.Finite.SmoothAt φ q)
    (singularIdeal_le : φ.singularIdealIn ≤ F.toTarget.singularIdealIn) :
    ResolutionAtPrime φ q :=
  Factorisation.Finite.Resolution.ofAvoids F.toAvoids singularIdeal_le

/-- A resolution at a larger target prime also avoids every smaller target
prime. -/
theorem not_le_ofLE {p q : PrimeSpectrum Λ} (W : ResolutionAtPrime φ q)
    (hpq : p ≤ q) :
    ¬ W.toTarget.singularIdealIn ≤ p.asIdeal := sorry

end ResolutionAtPrime

/-- Situation 16.9.1 (Tag 07F7): an `R`-algebra map is resolvable at a
target prime if it admits a concrete resolution witness there. -/
@[stacks 07F7 "resolvable at a prime"]
def ResolvableAtPrime (φ : A →ₐ[R] Λ) (q : PrimeSpectrum Λ) : Prop :=
  Nonempty (ResolutionAtPrime φ q)

namespace ResolutionAtPrime

/-- A concrete resolution witnesses the corresponding resolvability
predicate. -/
theorem resolvable {φ : A →ₐ[R] Λ} {q : PrimeSpectrum Λ}
    (W : ResolutionAtPrime φ q) : φ.ResolvableAtPrime q := sorry

end ResolutionAtPrime

namespace ResolvableAtPrime

/-- A finite-presentation factorisation with the required singular-ideal
comparisons resolves the map at the target prime. -/
@[stacks 07F7 "resolvable factorisation witness"]
theorem of {φ : A →ₐ[R] Λ} {q : PrimeSpectrum Λ}
    (F : AlgHom.Factorisation.Finite φ)
    (hSing : φ.singularIdealIn ≤ F.toTarget.singularIdealIn)
    (hnot : ¬ F.toTarget.singularIdealIn ≤ q.asIdeal) :
    φ.ResolvableAtPrime q := sorry

/-- A categorical factorisation with finitely presented midpoint satisfying
the two singular-ideal comparisons resolves the map at the target prime. -/
theorem of_factorisation {φ : A →ₐ[R] Λ} {q : PrimeSpectrum Λ}
    (F : φ.Factorisation) [Algebra.FinitePresentation R F.mid]
    (hSing : φ.singularIdealIn ≤ F.toTarget.singularIdealIn)
    (hnot : ¬ F.toTarget.singularIdealIn ≤ q.asIdeal) :
    φ.ResolvableAtPrime q := sorry

/-- Concrete maps whose composite is the original map give a resolution when
their midpoint is finitely presented and their singular ideals compare in the
required directions. -/
theorem of_maps {φ : A →ₐ[R] Λ} {q : PrimeSpectrum Λ}
    {B : Type (max u v w)} [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B] (f : A →ₐ[R] B) (g : B →ₐ[R] Λ)
    (hcomp : g.comp f = φ)
    (hSing : φ.singularIdealIn ≤ g.singularIdealIn)
    (hnot : ¬ g.singularIdealIn ≤ q.asIdeal) :
    φ.ResolvableAtPrime q := sorry

/-- Resolution is preserved when a resolved map is precomposed by a map whose
composite transported singular ideal is already contained in that of the
intermediate source. -/
theorem comp {B : Type (max u v w)} [CommRing B] [Algebra R B]
    {q : PrimeSpectrum Λ} {g : B →ₐ[R] Λ}
    (hg : g.ResolvableAtPrime q) (f : A →ₐ[R] B)
    (hSing : (g.comp f).singularIdealIn ≤ g.singularIdealIn) :
    (g.comp f).ResolvableAtPrime q := sorry

/-- A finitely presented source resolves its map at every prime avoided by
the map's transported singular ideal. -/
theorem of_not_singularIdeal_le [Algebra.FinitePresentation R A]
    {φ : A →ₐ[R] Λ} {q : PrimeSpectrum Λ}
    (hnot : ¬ φ.singularIdealIn ≤ q.asIdeal) :
    φ.ResolvableAtPrime q := sorry

/-- If `p` is contained in `q`, a resolution at `q` is also a resolution at
`p`. -/
theorem of_le {φ : A →ₐ[R] Λ} {p q : PrimeSpectrum Λ}
    (hq : φ.ResolvableAtPrime q) (hpq : p ≤ q) :
    φ.ResolvableAtPrime p := sorry

end ResolvableAtPrime

end AlgHom
