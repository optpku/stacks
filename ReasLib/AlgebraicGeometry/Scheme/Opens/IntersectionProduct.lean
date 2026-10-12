/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The morphism from an intersection of opens to their product
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Opens

variable {X : Scheme.{u}}

/-- The canonical morphism from an intersection of two open subschemes to their product,
pairing the two restriction morphisms; this is the data owner used in Lemma 26.21.16. -/
@[stacks 01KW]
noncomputable def interToProduct (U V : X.Opens) :
    (U ⊓ V).toScheme ⟶ U.toScheme ⨯ V.toScheme :=
  prod.lift
    (Scheme.Hom.resLE (𝟙 X) U (U ⊓ V) inf_le_left)
    (Scheme.Hom.resLE (𝟙 X) V (U ⊓ V) inf_le_right)

/-- The first projection of `interToProduct U V` is restriction to `U`. -/
@[reassoc (attr := simp)]
theorem interToProduct_fst (U V : X.Opens) :
    interToProduct U V ≫ prod.fst =
      Scheme.Hom.resLE (𝟙 X) U (U ⊓ V) inf_le_left := sorry

/-- The second projection of `interToProduct U V` is restriction to `V`. -/
@[reassoc (attr := simp)]
theorem interToProduct_snd (U V : X.Opens) :
    interToProduct U V ≫ prod.snd =
      Scheme.Hom.resLE (𝟙 X) V (U ⊓ V) inf_le_right := sorry

/-- On a separated scheme, the intersection of two opens is a closed subscheme of their
product. -/
instance interToProduct_isClosedImmersion [X.IsSeparated] (U V : X.Opens) :
    IsClosedImmersion (interToProduct U V) := sorry

end AlgebraicGeometry.Scheme.Opens
