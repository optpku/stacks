module

public import Mathlib.Algebra.Algebra.Pi
public import ReasLib.RingTheory.RingHom.IndZariski

@[expose] public section

/-!
# Ind-(Zariski localization) ring homomorphisms

An ind-(Zariski localization) ring homomorphism is a filtered colimit of finite
products of principal localizations. The finite-stage property is expressed on
algebras and on morphisms of commutative rings, and implies the local-isomorphism
property. Consequently, every ind-(Zariski localization) is ind-Zariski.
-/

open CategoryTheory MorphismProperty RingHom

universe u v w

namespace Algebra

/-- An `R`-algebra is a finite product of principal localizations if it is
`R`-algebra equivalent to `Π i : Fin n, Localization.Away (f i)` for some
family `f : Fin n → R`. -/
def IsFiniteProductOfPrincipalLocalizations (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] : Prop :=
  ∃ (n : ℕ) (f : Fin n → R),
    Nonempty (((i : Fin n) → Localization.Away (f i)) ≃ₐ[R] S)

namespace IsFiniteProductOfPrincipalLocalizations

/-- An algebra is a finite product of principal localizations if and only if it
is equivalent to a finite product of `Localization.Away` algebras. -/
theorem iff {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    IsFiniteProductOfPrincipalLocalizations R S ↔
      ∃ (n : ℕ) (f : Fin n → R),
        Nonempty (((i : Fin n) → Localization.Away (f i)) ≃ₐ[R] S) :=
  sorry

/-- A principal localization is a one-factor finite product of principal
localizations. -/
theorem of_localizationAway {R : Type u} [CommRing R] (r : R) :
    IsFiniteProductOfPrincipalLocalizations R (Localization.Away r) :=
  sorry

/-- A standard open immersion is a finite product of principal localizations. -/
theorem of_isStandardOpenImmersion {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsStandardOpenImmersion R S] :
    IsFiniteProductOfPrincipalLocalizations R S :=
  sorry

/-- A finite product of finite products of principal localizations is again a
finite product of principal localizations. -/
theorem pi {R : Type u} {n : ℕ} (S : Fin n → Type u) [CommRing R]
    [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    (h : ∀ i, IsFiniteProductOfPrincipalLocalizations R (S i)) :
    IsFiniteProductOfPrincipalLocalizations R ((i : Fin n) → S i) :=
  sorry

/-- Finite products of principal localizations are local isomorphisms. -/
theorem isLocalIso {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : IsFiniteProductOfPrincipalLocalizations R S) : Algebra.IsLocalIso R S :=
  sorry

end IsFiniteProductOfPrincipalLocalizations

end Algebra

namespace CommRingCat

/-- The morphism property on `CommRingCat` consisting of finite products of
principal localizations. -/
abbrev finiteProductOfPrincipalLocalizations : MorphismProperty CommRingCat.{u} :=
  fun _ _ f ↦ @Algebra.IsFiniteProductOfPrincipalLocalizations _ _ _ _ f.hom.toAlgebra

/-- A morphism of commutative rings is a finite product of principal
localizations precisely when the induced algebra structure satisfies
`Algebra.IsFiniteProductOfPrincipalLocalizations`. -/
theorem finiteProductOfPrincipalLocalizations_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    finiteProductOfPrincipalLocalizations f ↔
      @Algebra.IsFiniteProductOfPrincipalLocalizations R S _ _ f.hom.toAlgebra :=
  sorry

/-- Finite products of principal localizations are local isomorphisms. -/
theorem finiteProductOfPrincipalLocalizations_le_localIso :
    (finiteProductOfPrincipalLocalizations : MorphismProperty CommRingCat.{u}) ≤ localIso :=
  sorry

/-- Finite products of principal localizations are invariant under
isomorphisms. -/
instance finiteProductOfPrincipalLocalizations_respectsIso :
    CommRingCat.finiteProductOfPrincipalLocalizations.RespectsIso :=
  sorry

end CommRingCat

namespace RingHom

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- A ring map has an ind-(Zariski localization) presentation in universe `w`
if it is a filtered colimit of finite products of principal localizations in
that universe. -/
abbrev IndZariskiLocalization.Raw (f : R →+* A) : Prop :=
  ind.{w, max u v, max u v + 1} CommRingCat.finiteProductOfPrincipalLocalizations
    (CommRingCat.ofHom f.ulift.{v, u})

/-- A ring map is an ind-(Zariski localization) when it is a filtered colimit
of finite products of principal localizations, with presentation universe equal
to the maximum of the endpoint universes. -/
abbrev IndZariskiLocalization (f : R →+* A) : Prop :=
  IndZariskiLocalization.Raw.{u, v, max u v} f

end

namespace IndZariskiLocalization

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- An arbitrary-size categorical presentation induces the canonical
ind-(Zariski localization) predicate. -/
theorem ofRaw (f : R →+* A) (h : IndZariskiLocalization.Raw.{u, v, w} f) :
    f.IndZariskiLocalization :=
  sorry

/-- An ind-(Zariski localization) is ind-Zariski. -/
theorem indZariski (f : R →+* A) (h : f.IndZariskiLocalization) : f.IndZariski :=
  sorry

end

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- A finite product of principal localizations is an ind-(Zariski
localization). -/
theorem of_finiteProduct (h : Algebra.IsFiniteProductOfPrincipalLocalizations R A) :
    (algebraMap R A).IndZariskiLocalization :=
  sorry

/-- A principal localization map is an ind-(Zariski localization). -/
theorem of_localizationAway (r : R) :
    (algebraMap R (Localization.Away r)).IndZariskiLocalization :=
  sorry

end

end IndZariskiLocalization

end RingHom
