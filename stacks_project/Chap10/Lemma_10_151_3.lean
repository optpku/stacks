module

public import ReasLib.RingTheory.Unramified.Kaehler
public import ReasLib.RingTheory.Unramified.Closure
public import ReasLib.RingTheory.Unramified.Basic
import StacksCheckRecall

/-!
# Closure and approximation properties of unramified maps

@stack 00UV
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

/-! Lemma 10.151.3 (00UV): generic closure properties. -/

@[stacks 00UV "unramified base change"]
#check @Algebra.Unramified.baseChange

@[stacks 00UV "composition of unramified maps"]
#check @Algebra.Unramified.comp

@[stacks 00UV "principal localizations are unramified"]
#check @Algebra.Unramified.of_isLocalization_Away

@[stacks 00UV "quotients are unramified"]
#check @Algebra.Unramified.quotient

@[stacks 00UV "G-unramified base change"]
#check @Algebra.GUnramified.baseChange

@[stacks 00UV "composition of G-unramified maps"]
#check @Algebra.GUnramified.comp

@[stacks 00UV "principal localizations are G-unramified"]
#check @Algebra.GUnramified.of_localizationAway

@[stacks 00UV "finitely generated quotients are G-unramified"]
#check @Algebra.GUnramified.quotient_of_fg

@[stacks 00UV "etale maps are G-unramified"]
#check @Algebra.GUnramified.of_etale

/-! The four Kähler criteria, each in finite-type and finite-presentation form. -/

@[stacks 00UV "localized Kahler criterion, finite type"]
#check @Algebra.UnramifiedAt.of_subsingleton_localizedKaehler

@[stacks 00UV "localized Kahler criterion, finite presentation"]
#check @Algebra.GUnramifiedAt.of_subsingleton_localizedKaehler

@[stacks 00UV "Kahler fiber criterion, finite type"]
#check @Algebra.UnramifiedAt.of_subsingleton_kaehlerFiber

@[stacks 00UV "Kahler fiber criterion, finite presentation"]
#check @Algebra.GUnramifiedAt.of_subsingleton_kaehlerFiber

@[stacks 00UV "closed-fiber localized Kahler criterion, finite type"]
#check @Algebra.UnramifiedAt.of_subsingleton_fiberKaehlerLocalized

@[stacks 00UV "closed-fiber localized Kahler criterion, finite presentation"]
#check @Algebra.GUnramifiedAt.of_subsingleton_fiberKaehlerLocalized

@[stacks 00UV "closed-fiber residue criterion, finite type"]
#check @Algebra.UnramifiedAt.of_subsingleton_fiberKaehlerFiber

@[stacks 00UV "closed-fiber residue criterion, finite presentation"]
#check @Algebra.GUnramifiedAt.of_subsingleton_fiberKaehlerFiber

@[stacks 00UV "canonical localized Kahler characterization"]
#check @Algebra.IsUnramifiedAt.iff_subsingleton_localizedKaehler

@[stacks 00UV "canonical Kahler-fiber characterization"]
#check @Algebra.IsUnramifiedAt.iff_subsingleton_kaehlerFiber

@[stacks 00UV "closed-fiber Kahler base comparison"]
#check @PrimeSpectrum.Fiber.kaehlerBase

@[stacks 00UV "closed-fiber Kahler residue comparison"]
#check @PrimeSpectrum.Fiber.kaehlerResidue

/-! Local-to-global closure. -/

@[stacks 00UV "unramifiedness from a principal-open cover"]
#check @Algebra.Unramified.of_awayCover

@[stacks 00UV "unramifiedness at every prime"]
#check @Algebra.Unramified.of_at

@[stacks 00UV "canonical pointwise-to-global unramifiedness"]
#check @Algebra.Unramified.of_isUnramifiedAt

@[stacks 00UV "G-unramifiedness from a principal-open cover"]
#check @Algebra.GUnramified.of_awayCover

@[stacks 00UV "G-unramifiedness at every prime"]
#check @Algebra.GUnramified.of_at

@[stacks 00UV "canonical pointwise-to-global G-unramifiedness"]
#check @Algebra.GUnramified.of_isUnramifiedAt

/-- Lemma 10.151.3 (00UV), approximation clause for G-unramified maps: a G-unramified algebra
descends from finite-type algebras over `Z`. -/
@[stacks 00UV "G-unramified approximation"]
theorem exists_gUnramified_approximation_over_Z [GUnramified R S] :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : Algebra ℤ R₀) (_ : FiniteType ℤ R₀)
      (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra R₀ S₀) (_ : GUnramified R₀ S₀)
      (_ : Algebra R₀ R), Nonempty ((R ⊗[R₀] S₀) ≃ₐ[R] S) := sorry

/-- Lemma 10.151.3 (00UV), approximation clause for unramified maps: an unramified algebra is a
quotient of a base change from finite-type algebras over `Z`. -/
@[stacks 00UV "unramified approximation"]
theorem exists_unramified_approximation_over_Z [Unramified R S] :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : Algebra ℤ R₀) (_ : FiniteType ℤ R₀)
      (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra R₀ S₀) (_ : Unramified R₀ S₀)
      (_ : Algebra R₀ R), ∃ φ : R ⊗[R₀] S₀ →ₐ[R] S, Function.Surjective φ := sorry

end Algebra
