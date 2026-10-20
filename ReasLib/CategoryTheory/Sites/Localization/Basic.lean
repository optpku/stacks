module

public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Tactic.CrossRefAttribute

/-!
# Slice-site localization

For a site `(C, J)` and an object `U`, the slice site `(C / U, J.over U)`
has a canonical morphism of topoi to `(C, J)`. This leaf owns that construction
when the pointwise right Kan extensions required by cocontinuous pushforward
are available. More refined representable and base-change comparisons belong in
separate leaves; in particular, an arbitrary slice localization is not asserted
to be an embedding.
-/

@[expose] public section

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) (U : C)
variable [HasSheafify (J.over U) (Type (max u v))]
variable [forall F : (Over U)ᵒᵖ ⥤ Type (max u v),
  (Over.forget U).op.HasPointwiseRightKanExtension F]

/-- The morphism of topoi induced by the cocontinuous forgetful functor from the slice site at
`U` to the ambient site. -/
@[stacks 04IX "(2), localization morphism"]
noncomputable def localizationMorphism :
    MorphismOfTopoiIn J (J.over U) :=
  (Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J

end CategoryTheory.GrothendieckTopology
