module

public import ReasLib.CategoryTheory.MorphismProperty.Localization.RightFraction
import StacksCheckRecall

@[expose] public section

universe v u w

namespace CategoryTheory

open MorphismProperty Localization
open MorphismProperty.RightFraction

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasRightCalculusOfFractions]

/- The source needs the explicit right-fraction formula and strict universal property under a
right calculus of fractions. ReasLib's `RightFraction.mapQ_ofHom` is the canonical-localization
specialization of mathlib's general right-fraction formula, so callers need not pass the
localization functor or its inversion proof. The strict universal property remains mathlib's
canonical `Localization.strictUniversalPropertyFixedTargetQ`. -/

/- Lemma 4.27.16 (1): for a right multiplicative system `W`, the canonical functor `W.Q` sends
`f : X ⟶ Y` to the morphism represented by the right fraction with denominator `𝟙 X` and
numerator `f`. -/
@[stacks 04VK "canonical functor with its right-fraction formula"]
#check ((fun {X Y : C} (f : X ⟶ Y) => RightFraction.mapQ_ofHom (W := W) f) :
  ∀ {X Y : C} (f : X ⟶ Y),
    (RightFraction.ofHom W f).mapQ = W.Q.map f)

/- Lemma 4.27.16 (2): the canonical localization functor sends every morphism in `W` to an
isomorphism. -/
@[stacks 04VK "morphisms in the right multiplicative system become isomorphisms"]
#check (W.Q_inverts : W.IsInvertedBy W.Q)

variable (D : Type w) [Category D]

/- Lemma 4.27.16 (3): every functor from `C` to `D` that inverts `W` factors uniquely, with
strict equality, through `W.Q`. -/
@[stacks 04VK "strict existence and uniqueness of the localization factorization"]
#check (Localization.strictUniversalPropertyFixedTargetQ W D :
  Localization.StrictUniversalPropertyFixedTarget W.Q W D)

end CategoryTheory
