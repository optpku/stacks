module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Complete intersections over a field

This module owns the global and local complete-intersection conditions for
algebras over a field.
-/

universe u v

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]

/-- A `k`-algebra is a global complete intersection when it is subsingleton or
admits a finite presentation whose presentation dimension equals its Krull
dimension. -/
@[stacks 00S9]
class IsGlobalCompleteIntersection (k : Type u) (S : Type v) [Field k] [CommRing S]
    [Algebra k S] : Prop where
  /-- A finite presentation of the expected dimension, unless the algebra is subsingleton. -/
  presentation_or_subsingleton :
    Subsingleton S ∨
      ∃ (n c : ℕ) (P : Algebra.Presentation k S (Fin n) (Fin c)),
        ringKrullDim S = P.dimension

/-- The global complete-intersection condition is exactly its finite-presentation dimension
criterion, together with the subsingleton convention. -/
@[stacks 00S9 "global complete-intersection specification"]
theorem isGlobalCompleteIntersection_iff :
    IsGlobalCompleteIntersection k S ↔
      Subsingleton S ∨
        ∃ (n c : ℕ) (P : Algebra.Presentation k S (Fin n) (Fin c)),
          ringKrullDim S = P.dimension := sorry

namespace IsGlobalCompleteIntersection

/-- Build a global complete intersection from the presentation-dimension criterion or the
subsingleton convention. -/
theorem of_presentation_or_subsingleton
    (h : Subsingleton S ∨
      ∃ (n c : ℕ) (P : Algebra.Presentation k S (Fin n) (Fin c)),
        ringKrullDim S = P.dimension) :
    IsGlobalCompleteIntersection k S := sorry

/-- Global complete intersections are invariant under equivalences of `k`-algebras. -/
theorem of_algEquiv {T : Type*} [CommRing T] [Algebra k T]
    (hS : IsGlobalCompleteIntersection k S) (e : S ≃ₐ[k] T) :
    IsGlobalCompleteIntersection k T := sorry

/-- A global complete-intersection algebra is finitely presented over its base field. -/
instance instFinitePresentation [h : IsGlobalCompleteIntersection k S] :
    Algebra.FinitePresentation k S := sorry

/-- The quotient-presentation characterization of a global complete intersection. -/
theorem quotientPresentation_or_subsingleton [IsGlobalCompleteIntersection k S] :
    Subsingleton S ∨
      ∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) k),
        Nonempty ((MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)) ≃ₐ[k] S) ∧
          ringKrullDim S = n - c := sorry

/-- Subsingleton algebras are global complete intersections by convention. -/
instance instOfSubsingleton [Subsingleton S] : IsGlobalCompleteIntersection k S := sorry

end IsGlobalCompleteIntersection

/-- A `k`-algebra is a local complete intersection when finitely many basic
opens cover its spectrum and each corresponding localization is a global
complete intersection. -/
@[stacks 00S9]
class IsLocalCompleteIntersection (k : Type u) (S : Type v) [Field k] [CommRing S]
    [Algebra k S] : Prop where
  /-- A finite basic-open cover by global complete intersections. -/
  exists_basicOpen_cover :
    ∃ s : Finset S,
      Ideal.span (s : Set S) = ⊤ ∧
        ∀ g ∈ s, IsGlobalCompleteIntersection k (Localization.Away g)

/-- The local complete-intersection condition is exactly the existence of a finite basic-open
cover by global complete intersections. -/
@[stacks 00S9 "local complete-intersection specification over a field"]
theorem isLocalCompleteIntersection_iff :
    IsLocalCompleteIntersection k S ↔
      ∃ s : Finset S, Ideal.span (s : Set S) = ⊤ ∧
        ∀ g ∈ s, IsGlobalCompleteIntersection k (Localization.Away g) := sorry

namespace IsLocalCompleteIntersection

/-- Build a local complete intersection from a finite basic-open cover by global complete
intersections. -/
theorem of_basicOpen_cover
    (h : ∃ s : Finset S, Ideal.span (s : Set S) = ⊤ ∧
      ∀ g ∈ s, IsGlobalCompleteIntersection k (Localization.Away g)) :
    IsLocalCompleteIntersection k S := sorry

/-- A local complete-intersection algebra is finitely presented over its base field. -/
instance instFinitePresentation [h : IsLocalCompleteIntersection k S] :
    Algebra.FinitePresentation k S := sorry

/-- Every global complete intersection is a local complete intersection. -/
instance instOfGlobal [IsGlobalCompleteIntersection k S] :
    IsLocalCompleteIntersection k S := sorry

end IsLocalCompleteIntersection
