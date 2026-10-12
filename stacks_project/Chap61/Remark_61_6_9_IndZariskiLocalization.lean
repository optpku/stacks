/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.MorphismProperty.Ind
public import Mathlib.RingTheory.LocalIso
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap61.Definition_61_4_1_IndZariski

@[expose] public section

/-!
# Ind-(Zariski localization) ring homomorphisms

Bhatt–Scholze work with filtered colimits of finite products of principal
localizations.  This module owns that strictly stronger stage as a morphism
property on `CommRingCat` and as a ring-map predicate
`RingHom.IndZariskiLocalization`, parallel to `RingHom.IndZariski` and
`RingHom.IndEtale`.  The working Stacks owner remains `RingHom.IndZariski`;
the comparison `IndZariskiLocalization → IndZariski` is recorded below.  The
preference for ind-Zariski on formal grounds, and the analogy with ind-étale,
are not theorems.
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

/-- The representation-level ind-(Zariski localization) predicate with an
arbitrary universe for the filtered presentation. -/
abbrev IndZariskiLocalization.Raw (f : R →+* A) : Prop :=
  ind.{w, max u v, max u v + 1} CommRingCat.finiteProductOfPrincipalLocalizations
    (CommRingCat.ofHom f.ulift.{v, u})

/-- A ring map is an ind-(Zariski localization) when it is a filtered colimit
of finite products of principal localizations. The public owner uses the
canonical endpoint universe; arbitrary presentation sizes belong to
`IndZariskiLocalization.Raw`. -/
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
