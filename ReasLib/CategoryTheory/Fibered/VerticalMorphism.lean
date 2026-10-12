/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Vertical morphisms over a base

For an arbitrary functor `p : E ⥤ B`, this module packages the morphisms of `E` lying over an
identity of `B` as a `MorphismProperty`.  The definition uses mathlib's endpoint-aware
`Functor.IsHomLift`, so it does not expose definitional equalities between base objects.
-/

@[expose] public section

universe uB uE uE' vB vE vE'

namespace CategoryTheory
namespace Functor

variable {B : Type uB} {E : Type uE}
variable [Category.{vB} B] [Category.{vE} E]

/-- Definition 4.32.1 (Stacks 003Y): the morphism property consisting of arrows that lie over
an identity morphism of the base. -/
@[stacks 003Y "vertical morphisms over identities"]
def verticalMorphisms (p : E ⥤ B) : MorphismProperty E :=
  fun {_ _} f ↦ ∃ U : B, p.IsHomLift (𝟙 U) f

namespace verticalMorphisms

/-- A morphism is vertical exactly when its image is an identity transport between equal base
objects.  This is the equality-based interface to the endpoint-aware `IsHomLift` owner. -/
theorem iff_map_eqToHom (p : E ⥤ B) {X Y : E} (f : X ⟶ Y) :
    p.verticalMorphisms f ↔
      ∃ h : p.obj X = p.obj Y, p.map f = eqToHom h := sorry

/-- Vertical morphisms contain identities and are closed under composition. -/
instance isMultiplicative (p : E ⥤ B) :
    (p.verticalMorphisms).IsMultiplicative := sorry

variable {E' : Type uE'} [Category.{vE'} E']

/-- A functor commuting strictly with projections to the same base sends vertical morphisms to
vertical morphisms. -/
theorem map_of_comp_eq {p : E ⥤ B} {q : E' ⥤ B}
    (F : E ⥤ E') (w : F ⋙ q = p) {X Y : E} {f : X ⟶ Y}
    (hf : p.verticalMorphisms f) :
    q.verticalMorphisms (F.map f) := sorry

end verticalMorphisms

end Functor
end CategoryTheory
