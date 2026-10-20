module

public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps between prime-complement localizations

The primitive localization map is owned by `IsLocalization.map`.  This leaf gives the
prime-complement specialization in a neutral namespace, together with its algebra-map and
surjectivity bridges.  The target is written using the mapped submonoid, so the construction does
not depend on a temporary `Algebra A B := f.toRingHom.toAlgebra` instance.
-/

@[expose] public section

universe u v w

namespace Localization.AtPrime

variable {A : Type u} {B : Type v}
variable [CommSemiring A] [CommSemiring B]

/-- Tag `087P`: the canonical ring map induced by `f` between prime-complement localizations. -/
@[stacks 087P "prime-complement localization map"]
noncomputable abbrev map (f : A →+* B) (p : Ideal A) [p.IsPrime] :
    Localization.AtPrime p →+*
      Localization (Submonoid.map f p.primeCompl) :=
  IsLocalization.map
    (Localization (Submonoid.map f p.primeCompl)) f p.primeCompl.le_comap_map

/-- Tag `087P`: the prime-complement localization map sends a source generator to the localized
image of its numerator. -/
@[simp, stacks 087P "prime-complement localization map on generators"]
theorem map_apply_algebraMap (f : A →+* B) (p : Ideal A) [p.IsPrime] (x : A) :
    map f p (algebraMap A (Localization.AtPrime p) x) =
      algebraMap B (Localization (Submonoid.map f p.primeCompl)) (f x) := sorry

/-- Tag `087P`: a surjective ring map remains surjective after prime-complement localization. -/
@[stacks 087P "surjectivity of prime-complement localization map"]
theorem map_surjective_of_surjective (f : A →+* B) (p : Ideal A) [p.IsPrime]
    (hf : Function.Surjective f) :
    Function.Surjective (map f p) := sorry

end Localization.AtPrime

namespace AlgHom.Localization.AtPrime

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [CommSemiring A] [CommSemiring B]
variable [Algebra R A] [Algebra R B]

/-- Tag `087P`: compatibility of the prime-complement localization map with a base algebra. -/
@[stacks 087P "prime-complement localization algebra-map compatibility"]
theorem map_commutes (f : A →ₐ[R] B) (p : Ideal A) [p.IsPrime] (r : R) :
    Localization.AtPrime.map f.toRingHom p
        (algebraMap R (Localization.AtPrime p) r) =
      algebraMap R (Localization (Submonoid.map f.toRingHom p.primeCompl)) r := sorry

/-- Tag `087P`: the canonical `R`-algebra map induced by `f` between prime-complement
localizations. -/
@[stacks 087P "prime-complement localization algebra map"]
noncomputable def map (f : A →ₐ[R] B) (p : Ideal A) [p.IsPrime] :
    Localization.AtPrime p →ₐ[R]
      Localization (Submonoid.map f.toRingHom p.primeCompl) :=
  { toRingHom := _root_.Localization.AtPrime.map f.toRingHom p
    commutes' := map_commutes f p }

/-- Tag `087P`: the prime-complement localization algebra map sends a source generator to the
localized image of its numerator. -/
@[simp, stacks 087P "prime-complement localization algebra map on generators"]
theorem map_apply_algebraMap (f : A →ₐ[R] B) (p : Ideal A) [p.IsPrime] (x : A) :
    map f p (algebraMap A (Localization.AtPrime p) x) =
      algebraMap B (Localization (Submonoid.map f.toRingHom p.primeCompl)) (f x) := sorry

/-- Tag `087P`: a surjective algebra map remains surjective after prime-complement localization. -/
@[stacks 087P "surjectivity of prime-complement localization algebra map"]
theorem map_surjective_of_surjective (f : A →ₐ[R] B) (p : Ideal A) [p.IsPrime]
    (hf : Function.Surjective f) :
    Function.Surjective (map f p) := sorry

end AlgHom.Localization.AtPrime
