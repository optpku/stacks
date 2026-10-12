/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.Module
public import ReasLib.Algebra.Module.LocalizedModule.Equiv
public import ReasLib.RingTheory.Localization.AtPrime.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Kernels at prime-complement localizations

This leaf packages the canonical comparison between localizing the kernel of an algebra map and
the kernel of its prime-complement localization.  Mathlib owns the underlying
`AlgHom.toKerIsLocalization`; this interface fixes the canonical prime-complement model and
keeps the relative source-algebra action internal to the construction.
-/

@[expose] public section

universe u v w

namespace AlgHom.Localization.AtPrime

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/-- The canonical map from the kernel of an algebra homomorphism to the
kernel of its prime-complement localization. -/
noncomputable abbrev kernelMap (f : A →ₐ[R] B) (p : Ideal A) [p.IsPrime] :
    RingHom.ker f.toRingHom →ₗ[A] RingHom.ker (map f p).toRingHom :=
  RingHom.toKerIsLocalization (Localization.AtPrime p)
    (Localization (Submonoid.map f.toRingHom p.primeCompl))
    f.toRingHom p.primeCompl.le_comap_map

/-- The canonical kernel map is a localization at the prime complement. -/
theorem kernelMap_isLocalizedModule
    (f : A →ₐ[R] B) (p : Ideal A) [p.IsPrime] :
    IsLocalizedModule p.primeCompl (kernelMap f p) := sorry

/-- Tag `087P`: localizing the kernel of an `R`-algebra map at a prime complement is canonically
linearly equivalent over the local source ring to the kernel of the induced localized algebra map.
The temporary `A`-algebra structure on `B` is determined by `f` and is confined to this
construction. -/
@[stacks 087P "prime-localized algebra-map kernel comparison"]
noncomputable def kernelEquiv (f : A →ₐ[R] B) (p : Ideal A) [p.IsPrime] :=
  IsLocalizedModule.localizedEquiv p.primeCompl (Localization.AtPrime p)
    (kernelMap f p) (kernelMap_isLocalizedModule f p)

end AlgHom.Localization.AtPrime
