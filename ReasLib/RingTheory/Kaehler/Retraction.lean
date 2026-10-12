/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Smooth.Kaehler
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cotangent Modules of Algebra Retractions

The cotangent module of the kernel of an `R`-algebra retraction inherits
finiteness and projectivity from the Kahler differentials of the ambient
algebra. The retraction itself supplies its left-inverse law, so callers do
not carry a redundant equation.
-/

@[expose] public section

open scoped TensorProduct

namespace KaehlerDifferential.Retraction

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A retraction kernel has finite cotangent module whenever the ambient Kahler
differentials are finite. -/
@[stacks 05D5 "finite cotangent module of a retraction"]
theorem cotangent_finite
    (sigma : S →ₐ[R] R) [Module.Finite S Ω[S⁄R]] :
    Module.Finite R (RingHom.ker sigma).Cotangent := sorry

/-- A retraction kernel has projective cotangent module whenever the ambient Kahler
differentials are projective. -/
@[stacks 05D5 "projective cotangent module of a retraction"]
theorem cotangent_projective
    (sigma : S →ₐ[R] R) [Module.Projective S Ω[S⁄R]] :
    Module.Projective R (RingHom.ker sigma).Cotangent := sorry

/-- The cotangent module of a retraction kernel is finite projective when the
ambient Kahler differentials are finite projective. -/
@[stacks 05D5 "finite projective cotangent module of a retraction"]
theorem cotangent_finite_projective
    (sigma : S →ₐ[R] R) [Module.Finite S Ω[S⁄R]] [Module.Projective S Ω[S⁄R]] :
    Module.Finite R (RingHom.ker sigma).Cotangent ∧
      Module.Projective R (RingHom.ker sigma).Cotangent := sorry

end KaehlerDifferential.Retraction
