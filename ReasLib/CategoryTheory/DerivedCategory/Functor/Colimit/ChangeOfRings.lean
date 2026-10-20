module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.Point
public import ReasLib.CategoryTheory.Functor.Derived.Model
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived colimit and change of rings

Extension of scalars on module-valued presheaves is the right source-level model for the inverse
image of a morphism of constant ringed topoi.  This leaf owns that concrete functor, its derived
lift, the underived colimit comparison, and the resulting source-facing derived comparison.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe q u v wB wB' z

namespace CategoryTheory.DerivedColimit.ChangeOfRings

variable {C : Type u} [Category.{v} C]
variable {B : Type wB} {B' : Type wB'} [CommRing B] [CommRing B']

/-- Extension of scalars on module-valued presheaves, obtained by pointwise whiskering. -/
@[stacks 08Q8 "presheaf extension of scalars"]
abbrev presheafExtendScalars (φ : B →+* B') :
    (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B) ⥤
      (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB'} B') :=
  (Functor.whiskeringRight (Cᵒᵖ) (ModuleCat.{max wB' z, wB} B)
      (ModuleCat.{max wB' z, wB'} B')).obj
    (ModuleCat.extendScalars.{wB, wB', max wB' z} φ)

/-- The presheaf extension-of-scalars functor is additive. -/
@[stacks 08Q8 "additive presheaf extension of scalars"]
instance presheafExtendScalars_additive (φ : B →+* B') :
    (presheafExtendScalars (C := C) φ).Additive := sorry

/-- The homotopy-to-derived functor underlying presheaf extension of scalars. -/
@[stacks 08Q8 "presheaf extension of scalars to the derived category"]
abbrev presheafExtendScalarsToDerived (φ : B →+* B')
    [HasDerivedCategory.{q} (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B)]
    [HasDerivedCategory.{q} (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB'} B')] :
    HomotopyCategory (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B) (up ℤ) ⥤
      DerivedCategory (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB'} B') :=
  Functor.Homotopy.toDerived (presheafExtendScalars (C := C) φ)

/-- An explicit derived model for presheaf extension of scalars.  The functor and its counit are
concrete fields; the universal property is carried separately by `LeftDerived.Model`. -/
@[stacks 05SA "explicit presheaf change-of-rings model"]
abbrev PresheafModel (φ : B →+* B')
    [HasDerivedCategory.{q} (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B)]
    [HasDerivedCategory.{q} (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB'} B')] :=
  Functor.LeftDerived.Model
    (presheafExtendScalarsToDerived (C := C) φ)
    (DerivedCategory.Qh :
      HomotopyCategory (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B) (up ℤ) ⥤
        DerivedCategory (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B))
    (HomotopyCategory.quasiIso
      (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B) (up ℤ))

/-- The concrete derived presheaf extension carried by an explicit `PresheafModel`. -/
@[stacks 05SA "derived presheaf change of rings from an explicit model"]
noncomputable abbrev presheafDerivedExtendScalarsOfModel
    {φ : B →+* B'}
    [HasDerivedCategory.{q} (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B)]
    [HasDerivedCategory.{q} (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB'} B')]
    (M : PresheafModel (C := C) φ) :
    DerivedCategory (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B) ⥤
      DerivedCategory (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB'} B') :=
  M.functor

/-- The derived extension-of-scalars functor on module-valued presheaves. -/
@[stacks 08Q8 "derived presheaf extension of scalars"]
noncomputable def presheafDerivedExtendScalars
    (φ : B →+* B')
    [HasDerivedCategory.{q} (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B)]
    [HasDerivedCategory.{q} (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB'} B')]
    [Functor.HasLeftDerivedFunctor
      (presheafExtendScalarsToDerived (C := C) φ)
      (HomotopyCategory.quasiIso
        (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B) (up ℤ))] :
    DerivedCategory (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B) ⥤
      DerivedCategory (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB'} B') :=
  Functor.totalLeftDerived
    (presheafExtendScalarsToDerived (C := C) φ)
    (DerivedCategory.Qh :
      HomotopyCategory (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B) (up ℤ) ⥤
        DerivedCategory (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B))
    (HomotopyCategory.quasiIso
      (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B) (up ℤ))

/-- The localization counit of the canonical derived presheaf extension. -/
@[stacks 05SA "derived presheaf change-of-rings counit"]
noncomputable abbrev presheafDerivedExtendScalarsCounit
    (φ : B →+* B')
    [HasDerivedCategory.{q} (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B)]
    [HasDerivedCategory.{q} (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB'} B')]
    [Functor.HasLeftDerivedFunctor
      (presheafExtendScalarsToDerived (C := C) φ)
      (HomotopyCategory.quasiIso
        (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B) (up ℤ))] :
    (DerivedCategory.Qh :
      HomotopyCategory (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B) (up ℤ) ⥤
        DerivedCategory (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B)) ⋙
        presheafDerivedExtendScalars (C := C) φ ⟶
      presheafExtendScalarsToDerived (C := C) φ :=
  Functor.totalLeftDerivedCounit
    (presheafExtendScalarsToDerived (C := C) φ)
    (DerivedCategory.Qh :
      HomotopyCategory (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B) (up ℤ) ⥤
        DerivedCategory (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B))
    (HomotopyCategory.quasiIso
      (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B) (up ℤ))

/-- The canonical presheaf change-of-rings model, with concrete functor and counit fields. -/
@[stacks 05SA "canonical presheaf change-of-rings model"]
noncomputable def presheafDerivedExtendScalarsModel
    (φ : B →+* B')
    [HasDerivedCategory.{q} (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B)]
    [HasDerivedCategory.{q} (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB'} B')]
    [Functor.HasLeftDerivedFunctor
      (presheafExtendScalarsToDerived (C := C) φ)
      (HomotopyCategory.quasiIso
        (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B) (up ℤ))] :
    PresheafModel (C := C) φ where
  functor := presheafDerivedExtendScalars (C := C) φ
  counit := presheafDerivedExtendScalarsCounit (C := C) φ
  isLeftDerived := sorry

/-- The counit carried by a specified presheaf change-of-rings model. -/
@[stacks 05SA "specified presheaf change-of-rings counit"]
abbrev presheafDerivedExtendScalarsOfModelCounit
    {φ : B →+* B'}
    [HasDerivedCategory.{q} (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B)]
    [HasDerivedCategory.{q} (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB'} B')]
    (M : PresheafModel (C := C) φ) :=
  M.counit

/-- The left-derived law carried by a specified presheaf change-of-rings model. -/
@[stacks 05SA "specified presheaf change-of-rings universal property"]
abbrev presheafDerivedExtendScalarsOfModel_isLeftDerived
    {φ : B →+* B'}
    [HasDerivedCategory.{q} (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B)]
    [HasDerivedCategory.{q} (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB'} B')]
    (M : PresheafModel (C := C) φ) :=
  M.isLeftDerived

/-- Extension of scalars commutes with the presheaf colimit over a point. -/
@[stacks 08Q8 "underived colimit change of rings"]
noncomputable def colimitExtendScalarsIso (φ : B →+* B')
    [HasColimitsOfShape Cᵒᵖ (ModuleCat.{max wB' z, wB} B)]
    [HasColimitsOfShape Cᵒᵖ (ModuleCat.{max wB' z, wB'} B')] :
    presheafExtendScalars (C := C) φ ⋙
        (colim : (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB'} B') ⥤
          ModuleCat.{max wB' z, wB'} B') ≅
      (colim : (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B) ⥤
        ModuleCat.{max wB' z, wB} B) ⋙
        ModuleCat.extendScalars.{wB, wB', max wB' z} φ :=
  (preservesColimitNatIso
    (ModuleCat.extendScalars.{wB, wB', max wB' z} φ)).symm

/-- Lemma 21.39.6 (08Q8): derived lower shriek commutes with extension of scalars. -/
@[stacks 08Q8]
theorem lowerShriek_isomorphic
    (φ : B →+* B')
    [hasModuleLeftDerived : Functor.HasLeftDerivedFunctor
      (ModuleCat.extendScalarsToDerived.{wB, wB', max wB' z} φ)
      (HomotopyCategory.quasiIso (ModuleCat.{max wB' z, wB} B) (up ℤ))]
    [HasColimitsOfShape Cᵒᵖ (ModuleCat.{max wB' z, wB} B)]
    [HasColimitsOfShape Cᵒᵖ (ModuleCat.{max wB' z, wB'} B')]
    [HasDerivedCategory.{q} (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B)]
    [HasDerivedCategory.{q} (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB'} B')]
    [Functor.HasLeftDerivedFunctor
      (presheafExtendScalarsToDerived (C := C) φ)
      (HomotopyCategory.quasiIso
        (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B) (up ℤ))]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C (ModuleCat.{max wB' z, wB} B) :
        HomotopyCategory (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B) (up ℤ) ⥤
          DerivedCategory (ModuleCat.{max wB' z, wB} B))
      (HomotopyCategory.quasiIso
        (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B) (up ℤ))]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C (ModuleCat.{max wB' z, wB'} B') :
        HomotopyCategory (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB'} B') (up ℤ) ⥤
          DerivedCategory (ModuleCat.{max wB' z, wB'} B'))
      (HomotopyCategory.quasiIso
        (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB'} B') (up ℤ))] :
    IsIsomorphic
      (presheafDerivedExtendScalars (C := C) φ ⋙
        categoryOverPointDerivedColimit C (ModuleCat.{max wB' z, wB'} B'))
      (categoryOverPointDerivedColimit C (ModuleCat.{max wB' z, wB} B) ⋙
        ModuleCat.derivedExtensionOfScalars.{wB, wB', max wB' z} φ) := sorry

/-- The change-of-rings comparison with an explicitly selected presheaf derived model.  This is
the model-facing entry point; the preceding theorem is the canonical choice specialization. -/
@[stacks 08Q8 "underived colimit change of rings for an explicit model"]
theorem lowerShriek_isomorphic_of_model
    (φ : B →+* B')
    [hasModuleLeftDerived : Functor.HasLeftDerivedFunctor
      (ModuleCat.extendScalarsToDerived.{wB, wB', max wB' z} φ)
      (HomotopyCategory.quasiIso (ModuleCat.{max wB' z, wB} B) (up ℤ))]
    [HasColimitsOfShape Cᵒᵖ (ModuleCat.{max wB' z, wB} B)]
    [HasColimitsOfShape Cᵒᵖ (ModuleCat.{max wB' z, wB'} B')]
    [HasDerivedCategory.{q} (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B)]
    [HasDerivedCategory.{q} (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB'} B')]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C (ModuleCat.{max wB' z, wB} B) :
        HomotopyCategory (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B) (up ℤ) ⥤
          DerivedCategory (ModuleCat.{max wB' z, wB} B))
      (HomotopyCategory.quasiIso
        (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB} B) (up ℤ))]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C (ModuleCat.{max wB' z, wB'} B') :
        HomotopyCategory (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB'} B') (up ℤ) ⥤
          DerivedCategory (ModuleCat.{max wB' z, wB'} B'))
      (HomotopyCategory.quasiIso
        (Cᵒᵖ ⥤ ModuleCat.{max wB' z, wB'} B') (up ℤ))] :
    (M : PresheafModel (C := C) φ) →
    IsIsomorphic
      (M.functor ⋙ categoryOverPointDerivedColimit C (ModuleCat.{max wB' z, wB'} B'))
      (categoryOverPointDerivedColimit C (ModuleCat.{max wB' z, wB} B) ⋙
        ModuleCat.derivedExtensionOfScalars.{wB, wB', max wB' z} φ) := sorry

end CategoryTheory.DerivedColimit.ChangeOfRings
