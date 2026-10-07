module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.CategoryTheory.Functor.Derived.Model
import Mathlib.Tactic.CrossRefAttribute

/-!
# Explicit fixed-right derived tensor models

This leaf packages a selected fixed-right left-derived model without choosing a monoidal
structure on the derived category.  The canonical total left-derived functor can therefore be
compared with downstream models through their counits alone.
@stack 064M
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.DerivedTensor.Right

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [∀ K L : CochainComplex C ℤ,
  HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (up ℤ)]

/-- The localization used by fixed-right derived tensoring. -/
@[stacks 064M "fixed-right tensor localization"]
abbrev localization :
    HomotopyCategory C (up ℤ) ⥤ DerivedCategory C :=
  DerivedCategory.Qh

/-- The quasi-isomorphisms inverted by fixed-right derived tensoring. -/
@[stacks 064M "fixed-right tensor denominators"]
abbrev qis : MorphismProperty (HomotopyCategory C (up ℤ)) :=
  HomotopyCategory.quasiIso C (up ℤ)

/-- The canonical representative comparison used by every fixed-right derived-tensor model.

This is independent of the chosen tensor model: it only records the standard representative of a
derived object and the comparison from its homotopy localization back to that object. -/
@[stacks 064M "fixed-right representative comparison"]
noncomputable def representativeIso (E : DerivedCategory C) :
    localization.obj
        ((HomotopyCategory.quotient C (up ℤ)).obj
          ((DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C).objPreimage E)) ≅ E :=
  (DerivedCategory.quotientCompQhIso C).app
      ((DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C).objPreimage E) ≪≫
    (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C).objObjPreimageIso E

/-- An explicit fixed-right derived tensor model for `E`, consisting of a selected functor,
its counit to `sourceFunctor E`, and the left-derived universal property. -/
@[stacks 064M "explicit fixed-right derived tensor model"]
abbrev Model (E : DerivedCategory C) :=
  Functor.LeftDerived.Model (sourceFunctor E) (localization (C := C)) (qis (C := C))

/-- Construct a fixed-right model from its selected functor, counit, and universal-property law. -/
@[stacks 064M "fixed-right model constructor"]
def Model.of (E : DerivedCategory C)
    (functor : DerivedCategory C ⥤ DerivedCategory C)
    (counit : localization (C := C) ⋙ functor ⟶ sourceFunctor E)
    (h : functor.IsLeftDerivedFunctor counit (qis (C := C))) : Model E :=
  Functor.LeftDerived.Model.of functor counit h

/-- The canonical explicit model carried by fixed-right total derived tensoring. -/
@[stacks 064M "canonical fixed-right derived tensor model"]
noncomputable def canonicalModel (E : DerivedCategory C) [Has (C := C)] : Model E :=
  Functor.LeftDerived.Model.of (functor E) (counit E) inferInstance

/-- Transport the canonical fixed-right counit to an isomorphic functor. -/
@[stacks 064M "transported fixed-right derived tensor counit"]
noncomputable def counitOfIso (E : DerivedCategory C) [Has (C := C)]
    (T : DerivedCategory C ⥤ DerivedCategory C) (e : functor E ≅ T) :
    localization (C := C) ⋙ T ⟶ sourceFunctor E :=
  (canonicalModel E).counitOfIso T e

/-- The canonical isomorphism from fixed-right total derived tensoring to an explicit model. -/
@[stacks 064M "fixed-right derived tensor model isomorphism"]
noncomputable abbrev modelIso (E : DerivedCategory C) [Has (C := C)]
    (M : Model E) : functor E ≅ M.functor :=
  (canonicalModel E).iso M

/-- Transporting the canonical counit along `modelIso E M` recovers the model counit. -/
@[stacks 064M "fixed-right model counit transport"]
theorem counitOfIso_modelIso (E : DerivedCategory C) [Has (C := C)]
    (M : Model E) :
    counitOfIso E M.functor (modelIso E M) = M.counit := by
  dsimp only [counitOfIso, Functor.LeftDerived.Model.counitOfIso]
  rw [← (canonicalModel E).iso_hom_counit M]
  simp

/-- The canonical model isomorphism intertwines the canonical and selected counits. -/
@[reassoc (attr := simp), stacks 064M "fixed-right model counit compatibility"]
theorem modelIso_counit (E : DerivedCategory C) [Has (C := C)]
    (M : Model E) :
    Functor.whiskerLeft (localization (C := C)) (modelIso E M).hom ≫ M.counit =
      counit E :=
  (canonicalModel E).iso_hom_counit M

/-- The objectwise canonical isomorphism from fixed-right total derived tensoring to an explicit
model. -/
@[stacks 064M "fixed-right derived tensor object model"]
noncomputable abbrev modelIsoApp (E : DerivedCategory C) [Has (C := C)]
    (M : Model E) (K : DerivedCategory C) :
    (functor E).obj K ≅ M.functor.obj K :=
  (modelIso E M).app K

/-- Objectwise counit compatibility for the canonical fixed-right model isomorphism. -/
@[reassoc (attr := simp), stacks 064M "fixed-right object model counit compatibility"]
theorem modelIsoApp_counit (E : DerivedCategory C) [Has (C := C)]
    (M : Model E) (K : HomotopyCategory C (up ℤ)) :
    (modelIsoApp E M ((localization (C := C)).obj K)).hom ≫ M.counit.app K =
      (counit E).app K :=
  (canonicalModel E).isoApp_hom_counit M K

end CategoryTheory.DerivedCategory.DerivedTensor.Right
