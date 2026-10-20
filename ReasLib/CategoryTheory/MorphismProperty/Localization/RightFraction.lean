module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-!
# Right fractions in the canonical localization

This leaf gives the short canonical-localization specialization of mathlib's
general `RightFraction.map` API.
-/

@[expose] public section

universe v u

namespace CategoryTheory.MorphismProperty

open Localization

variable {C : Type u} [Category.{v} C]

namespace RightFraction

variable {W : MorphismProperty C}
variable {X Y : C}

/-- The morphism in the canonical localization represented by a right fraction.

For an arbitrary functor inverting `W`, use the more general `RightFraction.map`; this
specialization fixes the canonical localization functor `W.Q`. -/
noncomputable def mapQ (φ : W.RightFraction X Y) :
    W.Q.obj X ⟶ W.Q.obj Y :=
  φ.map W.Q W.Q_inverts
/- Axiom audit: the source, target, denominator, numerator, and map are all inherited explicit
data from `φ` and `W.Q`. `mapQ` introduces no choice beyond the canonical localization owner. -/

/-- Postcomposing `mapQ` with the image of the denominator recovers the image of the numerator. -/
@[reassoc (attr := simp)]
theorem mapQ_s_comp (φ : W.RightFraction X Y) :
    W.Q.map φ.s ≫ φ.mapQ = W.Q.map φ.f := sorry
/- Proof strategy: specialize `RightFraction.map_s_comp_map` to `W.Q` and `W.Q_inverts`. -/

/-- A right fraction with identity denominator maps to the image of its numerator under the
canonical localization functor. -/
@[stacks 04VK "canonical functor with its right-fraction formula", simp]
theorem mapQ_ofHom (f : X ⟶ Y) [W.ContainsIdentities] :
    (RightFraction.ofHom W f).mapQ = W.Q.map f := sorry
/- Proof strategy: specialize `RightFraction.map_ofHom` to `W.Q` and `W.Q_inverts`. -/

/-- In a right calculus of fractions, two right fractions have the same canonical-localization
morphism exactly when they satisfy the standard right-fraction relation. -/
theorem mapQ_eq_iff [W.HasRightCalculusOfFractions]
    (φ ψ : W.RightFraction X Y) :
    φ.mapQ = ψ.mapQ ↔ RightFractionRel φ ψ := sorry
/- Proof strategy: specialize `RightFraction.map_eq_iff` to the canonical localization `W.Q`. -/

end RightFraction

end CategoryTheory.MorphismProperty
