module

import ReasLib.CategoryTheory.Filtration.FiniteInjective.Extension.Cochain
import ReasLib.CategoryTheory.Filtration.FiniteInjective.Extension.Homotopy
import StacksCheckRecall

@[expose] public section

/-!
# Equation 13.26.13.5

The bounded-below cochain and homotopy lifts are canonical receiver APIs on an additive filtered
extension. ReasLib exposes their object and morphism formulas together with quotient,
associated-graded, and forgetful comparisons, so downstream constructions retain all extension
comparison data.
-/

open CategoryTheory

universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory.FilteredObject.Finite.FilteredInjective

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]

variable {T : A ⥤+ B} (E : Extension T)

/- The termwise action of the extension on bounded-below cochain complexes. -/
#check E.cochain

/- Comparison with the original functor after taking any associated-graded piece at the cochain
level. -/
#check @Extension.Cochain.gradedIso

/- Forward naturality of the cochain associated-graded comparison. -/
#check @Extension.Cochain.gradedIso_hom_naturality

/- Comparison with the original functor after forgetting filtration at the cochain level. -/
#check @Extension.Cochain.forgetIso

/- Forward naturality of the cochain forgetful comparison. -/
#check @Extension.Cochain.forgetIso_hom_naturality

/- Equation 13.26.13.5 (`05U1`): an additive filtered extension acts termwise on bounded-below
complexes and hence induces the canonical bounded-below homotopy functor. -/
@[stacks 05U1] #check E.homotopy

/- Objectwise computation for the induced bounded-below homotopy functor. -/
#check @Extension.Homotopy.obj_obj

/- Morphismwise computation for the induced bounded-below homotopy functor. -/
#check @Extension.Homotopy.map_hom

/- Comparison with termwise mapping before passage to the homotopy category. -/
#check @Extension.Homotopy.quotientIso

/- Comparison with the original functor after forgetting the filtration. -/
#check @Extension.Homotopy.forgetIso

/- Comparison with the original functor after taking any associated-graded piece. -/
#check @Extension.Homotopy.gradedIso

/- Forward naturality of the associated-graded comparison. -/
#check @Extension.Homotopy.gradedIso_hom_naturality

/- Reverse naturality of the associated-graded comparison. -/
#check @Extension.Homotopy.gradedIso_inv_naturality

end CategoryTheory.FilteredObject.Finite.FilteredInjective
