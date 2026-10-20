module

public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Presentation
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue

/-!
# Comparing Selected Presentations with Pointwise Derived Values

@stack 05S9

At a source-defined object, the selected essentially constant presentation and Mathlib's
canonical pointwise limit or colimit compute the same object. This leaf isolates that comparison
from adjunction-specific applications and exposes its component formulas.
-/

@[expose] public section

open CategoryTheory Limits MorphismProperty

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']

namespace LeftDerived.DefinedAt

/-- The selected left-derived presentation is canonically isomorphic to the pointwise
left-derived value. -/
@[stacks 05S9 "selected presentation of a pointwise left-derived value"]
noncomputable def presentationIso
    {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    [hX : LeftDerived.DefinedAt F S X] :
    hX.presentation.pt ≅ LeftDerived.Value.obj F S X :=
  hX.isLimit.conePointUniqueUpToIso
    (limit.isLimit (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F))

/-- The forward selected-presentation comparison commutes with every cone projection. -/
@[reassoc (attr := simp), stacks 05S9 "left-derived presentation comparison, forward"]
theorem presentationIso_hom_fac
    {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    [hX : LeftDerived.DefinedAt F S X]
    (j : StructuredArrow (S.Q.obj X) S.Q) :
    hX.presentationIso.hom ≫
        limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) j =
      hX.presentation.π.app j := sorry

/-- The inverse selected-presentation comparison commutes with every cone projection. -/
@[reassoc (attr := simp), stacks 05S9 "left-derived presentation comparison, inverse"]
theorem presentationIso_inv_fac
    {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    [hX : LeftDerived.DefinedAt F S X]
    (j : StructuredArrow (S.Q.obj X) S.Q) :
    hX.presentationIso.inv ≫ hX.presentation.π.app j =
      limit.π (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) j := sorry

end LeftDerived.DefinedAt

namespace RightDerived.DefinedAt

/-- The selected right-derived presentation is canonically isomorphic to the pointwise
right-derived value. -/
@[stacks 05S9 "selected presentation of a pointwise right-derived value"]
noncomputable def presentationIso
    {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    [hX : RightDerived.DefinedAt F S X] :
    hX.presentation.pt ≅ RightDerived.Value.obj F S X :=
  hX.isColimit.coconePointUniqueUpToIso
    (colimit.isColimit (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F))

/-- The forward selected-presentation comparison commutes with every cocone leg. -/
@[reassoc (attr := simp), stacks 05S9 "right-derived presentation comparison, forward"]
theorem presentationIso_hom_fac
    {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    [hX : RightDerived.DefinedAt F S X]
    (j : CostructuredArrow S.Q (S.Q.obj X)) :
    hX.presentation.ι.app j ≫ hX.presentationIso.hom =
      colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) j := sorry

/-- The inverse selected-presentation comparison commutes with every cocone leg. -/
@[reassoc (attr := simp), stacks 05S9 "right-derived presentation comparison, inverse"]
theorem presentationIso_inv_fac
    {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    [hX : RightDerived.DefinedAt F S X]
    (j : CostructuredArrow S.Q (S.Q.obj X)) :
    colimit.ι (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) j ≫
        hX.presentationIso.inv =
      hX.presentation.ι.app j := sorry

end RightDerived.DefinedAt

end CategoryTheory.Functor
