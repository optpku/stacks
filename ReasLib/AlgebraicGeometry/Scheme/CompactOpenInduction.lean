module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Compact-open induction on schemes

This module gives an induction principle reducing a property of quasi-compact
opens on a quasi-compact, quasi-separated scheme to affine opens and unions
with an affine open. It is a scheme-facing specialization of
`AlgebraicGeometry.compact_open_induction_on`.
-/

@[expose] public section

open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]

/-- A property of quasi-compact opens on a quasi-compact, quasi-separated scheme
follows from the affine case and the union step with an affine open. -/
theorem compactOpen_induction_principle
    (P : X.Opens → Prop)
    (h_affine : ∀ U : X.affineOpens, P U)
    (h_union : ∀ (U : X.Opens), IsCompact (U : Set X) → ∀ V : X.affineOpens,
      P U → P V → P (U ⊓ V) → P (U ⊔ V)) :
    ∀ (U : X.Opens), IsCompact (U : Set X) → P U := sorry

/-- Under the induction hypotheses, the property holds for the whole scheme. -/
theorem compactOpen_induction_principle_top
    (P : X.Opens → Prop)
    (h_affine : ∀ U : X.affineOpens, P U)
    (h_union : ∀ (U : X.Opens), IsCompact (U : Set X) → ∀ V : X.affineOpens,
      P U → P V → P (U ⊓ V) → P (U ⊔ V)) :
    P (⊤ : X.Opens) := by
  exact compactOpen_induction_principle P h_affine h_union ⊤
    (isCompact_univ : IsCompact (Set.univ : Set X))

end AlgebraicGeometry.Scheme
