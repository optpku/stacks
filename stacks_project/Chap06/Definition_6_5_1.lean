module

public import Mathlib.Topology.Sheaves.Presheaf
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open CategoryTheory

/- Definition 6.5.1 (Tag 006N): a presheaf on a topological space `X` with values in a category
`C` is the canonical mathlib functor category `TopCat.Presheaf C X = (Opens X)ᵒᵖ ⥤ C`, whose
morphisms are natural transformations. -/
@[stacks 006N "presheaves on a topological space"]
recall TopCat.Presheaf

variable {X : TopCat.{w}} {C : Type u} [Category.{v} C]
variable {F G : X.Presheaf C} (φ : F ⟶ G)

/- A morphism of presheaves is a natural transformation, so compatibility with restriction along an
inclusion `i : V ⟶ U` is the canonical naturality identity `φ.naturality i.op`. -/
#check φ.naturality
