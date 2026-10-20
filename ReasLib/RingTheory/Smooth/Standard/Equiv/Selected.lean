module

public import ReasLib.RingTheory.Smooth.Standard.Element.Selected
import Mathlib.Tactic.CrossRefAttribute

/-!
# Selected standard data under algebra equivalences

Transport preserves embedding-indexed presentation data and the global
standard-element predicates. The selected index embeddings are unchanged by
`Algebra.Presentation.ofAlgEquiv`.
-/

@[expose] public section

universe u v w x y

namespace Algebra

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

namespace Presentation.IsElementaryFor

variable {ι : Type x} {σ : Type y} {c : ℕ}

/-- Elementary data in a fixed presentation transports along an algebra
equivalence. -/
@[stacks 07C7 "elementary standard data under algebra equivalence"]
theorem of_algEquiv
    {P : Presentation R A ι σ} {a : A}
    {cols : Fin c ↪ ι} {rows : Fin c ↪ σ}
    (h : P.IsElementaryFor a cols rows) (e : A ≃ₐ[R] B) :
    (P.ofAlgEquiv e).IsElementaryFor (e a) cols rows := sorry

/-- Elementary data is invariant under transport of its presentation along
an algebra equivalence. -/
theorem iff_of_algEquiv
    {P : Presentation R A ι σ} {a : A}
    {cols : Fin c ↪ ι} {rows : Fin c ↪ σ}
    (e : A ≃ₐ[R] B) :
    P.IsElementaryFor a cols rows ↔
      (P.ofAlgEquiv e).IsElementaryFor (e a) cols rows := sorry

end Presentation.IsElementaryFor

namespace Presentation.IsStrictlyFor

variable {ι : Type x} {σ : Type y} {c : ℕ}

/-- Strict data in a fixed presentation transports along an algebra
equivalence. -/
@[stacks 07C7 "strict standard data under algebra equivalence"]
theorem of_algEquiv
    {P : Presentation R A ι σ} {a : A} {rows : Fin c ↪ σ}
    (h : P.IsStrictlyFor a rows) (e : A ≃ₐ[R] B) :
    (P.ofAlgEquiv e).IsStrictlyFor (e a) rows := sorry

/-- Strict data is invariant under transport of its presentation along an
algebra equivalence. -/
theorem iff_of_algEquiv
    {P : Presentation R A ι σ} {a : A} {rows : Fin c ↪ σ}
    (e : A ≃ₐ[R] B) :
    P.IsStrictlyFor a rows ↔
      (P.ofAlgEquiv e).IsStrictlyFor (e a) rows := sorry

end Presentation.IsStrictlyFor

namespace IsElementaryStandard

/-- Elementary-standard elements transport along algebra equivalences. -/
@[stacks 07C7 "elementary standard elements under algebra equivalence"]
theorem of_algEquiv
    {a : A} (h : IsElementaryStandard R a) (e : A ≃ₐ[R] B) :
    IsElementaryStandard R (e a) := sorry

/-- Being elementary standard is invariant under algebra equivalence. -/
theorem iff_of_algEquiv
    {a : A} (e : A ≃ₐ[R] B) :
    IsElementaryStandard R a ↔ IsElementaryStandard R (e a) := sorry

end IsElementaryStandard

namespace IsStrictlyStandard

/-- Strictly-standard elements transport along algebra equivalences. -/
@[stacks 07C7 "strictly standard elements under algebra equivalence"]
theorem of_algEquiv
    {a : A} (h : IsStrictlyStandard R a) (e : A ≃ₐ[R] B) :
    IsStrictlyStandard R (e a) := sorry

/-- Being strictly standard is invariant under algebra equivalence. -/
theorem iff_of_algEquiv
    {a : A} (e : A ≃ₐ[R] B) :
    IsStrictlyStandard R a ↔ IsStrictlyStandard R (e a) := sorry

end IsStrictlyStandard

end Algebra
