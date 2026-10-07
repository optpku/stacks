module

public import Mathlib.CategoryTheory.Category.Cat.Terminal
public import ReasLib.CategoryTheory.Bicategory.Coyoneda
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Constructions.AsSmall
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Constructions.Constant.Basic

/-!
# The apex of the Cat-valued conical pseudolimit

The conical pseudolimit of a Cat-valued pseudodiagram is represented by strong
transformations from the constant diagram at the terminal category. This file contains only
that representable construction, the universe-resizing step, and the resulting apex category.

Evaluation, pseudonaturality, and the universal pseudocone are built in downstream files.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe wJ vJ uJ vCat uCat

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory

/-- The conical pseudolimit construction for Cat-valued pseudodiagrams of shape `J`.

Its value at `F : J ⥤ᵖ Cat` is the hom-category from the constant diagram at the terminal
category to `F`; hence its objects are pseudocones with a chosen object as apex. Strong
transformations and modifications act by postcomposition through `coyoneda₀`. -/
noncomputable def conicalPseudoLimit (J : Type uJ) [Bicategory.{wJ, vJ} J] :=
  coyoneda₀ (Pseudofunctor.const J (⊤_ Cat.{vCat, uCat}))

namespace ConicalPseudoLimit

variable {J : Type uJ} [Bicategory.{wJ, vJ} J]

/-- The category represented by the conical pseudolimit construction on `F`. Its objects
are strong transformations from the terminal constant diagram to `F`. -/
noncomputable abbrev coneCategory (F : J ⥤ᵖ Cat.{vCat, uCat}) :=
  (conicalPseudoLimit J).obj F

/-- Resize a Cat-valued pseudodiagram into a universe containing both the diagram shape
and all of its values.

Each value is replaced by its canonical `AsSmall` model. The common universe lets the
category of strong transformations serve as an object of the same ambient `Cat` as the
resized values. -/
def resizedDiagram (F : J ⥤ᵖ Cat.{vCat, uCat}) :
    J ⥤ᵖ Cat.{max wJ vJ uJ vCat uCat, max wJ vJ uJ vCat uCat} :=
  Pseudofunctor.asSmall.{max wJ vJ uJ} F

/-- The apex category of the canonical conical pseudolimit of the resized diagram.

This named owner insulates the universal cone API from the internal representable-functor
presentation. -/
noncomputable def apex (F : J ⥤ᵖ Cat.{vCat, uCat}) :
    Cat.{max wJ vJ uJ vCat uCat, max wJ vJ uJ vCat uCat} :=
  coneCategory (resizedDiagram F)

/- Data and axiom audit (mathlib 4.32):

`conicalPseudoLimit` is the explicit covariant representable at the terminal category.
`resizedDiagram` delegates to `Pseudofunctor.asSmall`, and `apex` is the corresponding
strong-transformation category. No object, functor, or universe-resizing datum is supplied
through a new existential choice at this layer. -/

end ConicalPseudoLimit

end Bicategory

end CategoryTheory
