module

public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Limits
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic

/-!
# Selected presentations of source-defined derived values

A source-defined derived value carries an essentially constant localization-indexed diagram.
This file exposes its selected cone or cocone, distinguished stage, split leg, and universal
property. Choice remains behind these named accessors and their specification API.
-/

@[expose] public section

open CategoryTheory Limits MorphismProperty

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']

namespace LeftDerived.DefinedAt

/-- The selected limit cone carried by a proof that the left-derived functor is source-defined
at `X`. All selected presentation data are projections of this single package. -/
@[stacks 05S9 "left-derived selected limit cone"]
noncomputable def limitCone {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    (hX : LeftDerived.DefinedAt F S X) :
    LimitCone (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) :=
  IsCofiltered.IsEssentiallyConstant.limitCone hX.isEssentiallyConstant

/-- The selected cone presentation carried by source-definedness at `X`. -/
@[stacks 05S9 "left-derived selected presentation"]
noncomputable def presentation {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    (hX : LeftDerived.DefinedAt F S X) :
    Cone (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) :=
  IsCofiltered.IsEssentiallyConstant.cone hX.isEssentiallyConstant

/-- The selected left-derived presentation is essentially constant. -/
@[stacks 05S9 "left-derived presentation specification"]
theorem presentation_isEssentiallyConstant
    {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    (hX : LeftDerived.DefinedAt F S X) :
    hX.presentation.IsEssentiallyConstant := sorry

/-- The selected stage of a source-defined left-derived presentation. -/
@[stacks 05S9 "left-derived selected stage"]
noncomputable def stage {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    (hX : LeftDerived.DefinedAt F S X) :
    StructuredArrow (S.Q.obj X) S.Q :=
  IsCofiltered.IsEssentiallyConstant.cone.stage hX.isEssentiallyConstant

/-- The split monomorphism carried by the selected left-derived presentation leg. -/
@[stacks 05S9 "left-derived selected split monomorphism"]
noncomputable def splitMono {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    (hX : LeftDerived.DefinedAt F S X) :
    SplitMono (hX.presentation.π.app hX.stage) :=
  IsCofiltered.IsEssentiallyConstant.cone.splitMono hX.isEssentiallyConstant

/-- The selected left-derived presentation carries the canonical limit universal property. -/
@[stacks 05S9 "left-derived presentation limit"]
noncomputable def isLimit {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    (hX : LeftDerived.DefinedAt F S X) :
    IsLimit hX.presentation :=
  hX.limitCone.isLimit

end LeftDerived.DefinedAt

namespace RightDerived.DefinedAt

/-- The selected colimit cocone carried by a proof that the right-derived functor is
source-defined at `X`. All selected presentation data are projections of this single package. -/
@[stacks 05S9 "right-derived selected colimit cocone"]
noncomputable def colimitCocone {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    (hX : RightDerived.DefinedAt F S X) :
    ColimitCocone (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) :=
  IsFiltered.IsEssentiallyConstant.colimitCocone hX.isEssentiallyConstant

/-- The selected cocone presentation carried by source-definedness at `X`. -/
@[stacks 05S9 "right-derived selected presentation"]
noncomputable def presentation {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    (hX : RightDerived.DefinedAt F S X) :
    Cocone (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) :=
  IsFiltered.IsEssentiallyConstant.cocone hX.isEssentiallyConstant

/-- The selected right-derived presentation is essentially constant. -/
@[stacks 05S9 "right-derived presentation specification"]
theorem presentation_isEssentiallyConstant
    {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    (hX : RightDerived.DefinedAt F S X) :
    hX.presentation.IsEssentiallyConstant := sorry

/-- The selected stage of a source-defined right-derived presentation. -/
@[stacks 05S9 "right-derived selected stage"]
noncomputable def stage {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    (hX : RightDerived.DefinedAt F S X) :
    CostructuredArrow S.Q (S.Q.obj X) :=
  IsFiltered.IsEssentiallyConstant.cocone.stage hX.isEssentiallyConstant

/-- The split epimorphism carried by the selected right-derived presentation leg. -/
@[stacks 05S9 "right-derived selected split epimorphism"]
noncomputable def splitEpi {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    (hX : RightDerived.DefinedAt F S X) :
    SplitEpi (hX.presentation.ι.app hX.stage) :=
  IsFiltered.IsEssentiallyConstant.cocone.splitEpi hX.isEssentiallyConstant

/-- The selected right-derived presentation carries the canonical colimit universal property. -/
@[stacks 05S9 "right-derived presentation colimit"]
noncomputable def isColimit {F : D ⥤ D'} {S : MorphismProperty D} {X : D}
    (hX : RightDerived.DefinedAt F S X) :
    IsColimit hX.presentation :=
  hX.colimitCocone.isColimit

end RightDerived.DefinedAt

end CategoryTheory.Functor
