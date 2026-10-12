/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Zero
public import ReasLib.CategoryTheory.Abelian.FunctorialInjectives

@[expose] public section

open CategoryTheory.Limits
open scoped CategoryTheory

universe v u

namespace CategoryTheory

noncomputable section

namespace AbelianPresheaf

variable (C : Type u) [Category.{v} C]

/-- The inclusion of the discrete category of objects of `Cᵒᵖ` into `Cᵒᵖ`. -/
abbrev objectInclusion : Discrete Cᵒᵖ ⥤ Cᵒᵖ :=
  Discrete.functor (fun X : Cᵒᵖ ↦ X)

/-- Restriction of an abelian presheaf to the discrete category of objects of `Cᵒᵖ`. -/
@[stacks 01DK "restriction to objects"]
abbrev objectRestriction :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤
      (Discrete Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :=
  (Functor.whiskeringLeft (Discrete Cᵒᵖ) Cᵒᵖ AddCommGrpCat.{max u v}).obj
    (objectInclusion C)

/-- Right Kan extension along the inclusion of the discrete category of objects. -/
@[stacks 01DK "right Kan extension from objects"]
abbrev objectCorestriction :
    (Discrete Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤
      (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :=
  (objectInclusion C).ran

namespace Discrete

section

variable [HasFunctorialInjectives AddCommGrpCat.{max u v}]

/-- The pointwise chosen injective target endofunctor on discrete abelian presheaves. -/
@[stacks 01DK "pointwise injective-target functor"]
noncomputable def injectiveFunctor :
    (Discrete Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤
      (Discrete Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) where
  obj F := Discrete.functor
    (fun X : Cᵒᵖ ↦ HasFunctorialInjectives.obj (F.obj (Discrete.mk X)))
  map {F G} φ :=
    Discrete.natTrans (fun X ↦ HasFunctorialInjectives.map (φ.app X))
  map_id := sorry
  map_comp := sorry

/-- The pointwise chosen monomorphism into the injective target on discrete abelian
presheaves. -/
@[stacks 01DK "pointwise injective embedding"]
noncomputable def injectiveι :
    𝟭 (Discrete Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⟶
      injectiveFunctor C where
  app F := Discrete.natTrans (fun X ↦ HasFunctorialInjectives.ι.app (F.obj X))
  naturality := sorry

/-- A discrete abelian presheaf is injective when all of its values are injective. -/
theorem injective_of_pointwise
    (J : Discrete Cᵒᵖ ⥤ AddCommGrpCat.{max u v})
    (hJ : ∀ X, Injective (J.obj X)) :
    Injective J := sorry

/-- Discrete abelian presheaves admit the pointwise functorial injective embedding. -/
noncomputable instance hasFunctorialInjectives :
    HasFunctorialInjectives (Discrete Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) where
  functor := injectiveFunctor C
  ι := injectiveι C
  mono_app := sorry
  injective_obj := sorry

end

end Discrete

variable [HasFunctorialInjectives AddCommGrpCat.{max u v}]

/-- Restriction to the discrete category of objects reflects zero abelian presheaves. -/
theorem objectRestriction_reflects_isZero
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v})
    (hF : IsZero ((objectRestriction C).obj F)) :
    IsZero F := sorry

/-- The injective-target endofunctor on abelian presheaves, explicitly obtained by restriction,
the pointwise construction, and right Kan extension. -/
@[stacks 01DK "injective-target functor"]
noncomputable def injectiveFunctor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤
      (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :=
  objectRestriction C ⋙ Discrete.injectiveFunctor C ⋙ objectCorestriction C

/-- The chosen injective target of an abelian presheaf. -/
noncomputable abbrev injective
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    Cᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  (injectiveFunctor C).obj F

/-- The map of chosen injective targets induced by a morphism of abelian presheaves. -/
noncomputable abbrev injectiveMap
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} (f : F ⟶ G) :
    injective C F ⟶ injective C G :=
  (injectiveFunctor C).map f

/-- The chosen embedding of an abelian presheaf into its injective target. -/
noncomputable def injectiveιApp
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    F ⟶ injective C F :=
  ((objectInclusion C).ranAdjunction AddCommGrpCat.{max u v}).homEquiv F _
    ((Discrete.injectiveι C).app ((objectRestriction C).obj F))

/-- The natural family of chosen embeddings of abelian presheaves into injective targets. -/
@[stacks 01DK "functorial injective embedding"]
noncomputable def injectiveι :
    𝟭 (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⟶
      injectiveFunctor C where
  app := injectiveιApp C
  naturality := sorry

/-- Abelian presheaves admit functorial injective embeddings, obtained by transferring the
pointwise construction along restriction and right Kan extension. -/
@[stacks 01DK]
noncomputable instance hasFunctorialInjectives :
    HasFunctorialInjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) where
  functor := injectiveFunctor C
  ι := injectiveι C
  mono_app := sorry
  injective_obj := sorry

end AbelianPresheaf

end

end CategoryTheory
