module

public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Cech.Augmentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Injective coefficients for presheaf-target hypercoverings

For an injective abelian sheaf, the augmented Cech sections complex of a presheaf-target
hypercovering has no positive cohomology.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory.HypercoveringOf.Cech

open Limits

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{max w v}]
variable {G : Cᵒᵖ ⥤ Type (max w v)}

/-- Lemma 25.6.3 [stacks 09VW] (1), degree-zero part: with coefficients in an injective
abelian sheaf, degree-zero Cech cohomology of a presheaf-target hypercovering is canonically
isomorphic to the coefficient sections over the target presheaf. -/
@[stacks 09VW "degree-zero injective presheaf-target hypercovering Cech cohomology"]
theorem cohomology_zero_isomorphic_targetSections_of_injective
    (K : HypercoveringOf J G)
    (I : Sheaf J AddCommGrpCat.{max w v}) [Injective I] :
    IsIsomorphic (cohomology K I 0) (targetSections G I) := sorry

/-- Lemma 25.6.3 [stacks 09VW] (2), positive-degree part: the Cech cohomology of a
presheaf-target hypercovering with coefficients in an injective abelian sheaf vanishes in every
strictly positive degree. Together with
`cohomology_zero_isomorphic_targetSections_of_injective`, this gives the full degreewise
statement. -/
@[stacks 09VW "positive-degree presheaf-target hypercovering Cech cohomology"]
theorem cohomology_isZero_of_injective_pos
    (K : HypercoveringOf J G)
    (I : Sheaf J AddCommGrpCat.{max w v}) [Injective I]
    {p : ℕ} (hp : 0 < p) :
    IsZero (cohomology K I p) := sorry

end CategoryTheory.HypercoveringOf.Cech
