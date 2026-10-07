module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.PseudoCoherent
public import Mathlib.RingTheory.RingHom.Flat
import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pseudo-coherent modules under flat scalar extension

This leaf is the degree-zero bridge from derived scalar extension to ordinary scalar extension.
Its public API uses an explicit flat ring homomorphism and independent ring/module universes, so
downstream code need not install local exactness or derived-functor instances.

@stack 066C
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe uR uS v

namespace CategoryTheory.ModuleCat.IsMPseudoCoherent

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

/-- Lemma 15.65.13 (1): flat extension of scalars preserves `m`-pseudo-coherent modules. -/
@[stacks 066C "(1), flat extension preserves m-pseudo-coherence"]
theorem extension_of_flat
    {M : ModuleCat.{v, uR} R} {m : ℤ} (hM : M.IsMPseudoCoherent m)
    (σ : R →+* S) (hσ : σ.Flat) :
    ((ModuleCat.extendScalars.{uR, uS, v} σ).obj M).IsMPseudoCoherent m := sorry
-- Proof strategy: identify ordinary extension of the degree-zero module with derived extension
-- using flatness of `σ`, then apply `DerivedCategory.IsMPseudoCoherent.extension`.

end CategoryTheory.ModuleCat.IsMPseudoCoherent

namespace CategoryTheory.ModuleCat.IsPseudoCoherent

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

/-- Lemma 15.65.13 (2): flat extension of scalars preserves pseudo-coherent modules. -/
@[stacks 066C "(2), flat extension preserves pseudo-coherence"]
theorem extension_of_flat
    {M : ModuleCat.{v, uR} R} (hM : M.IsPseudoCoherent)
    (σ : R →+* S) (hσ : σ.Flat) :
    ((ModuleCat.extendScalars.{uR, uS, v} σ).obj M).IsPseudoCoherent := sorry
-- Proof strategy: use the flat comparison between ordinary and derived extension and apply
-- `DerivedCategory.IsPseudoCoherent.extension`.

end CategoryTheory.ModuleCat.IsPseudoCoherent

end
