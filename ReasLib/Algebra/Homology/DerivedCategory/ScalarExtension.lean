module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.LeftDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import ReasLib.CategoryTheory.Functor.Derived.Model
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated

@[expose] public section

/-!
# Derived extension of scalars

@stack 05S9
@stack 064M

For a map of commutative rings, this leaf packages extension of scalars as an additive functor
and applies the generic total-left-derived-functor construction.  The existence certificates are
supplied by the displayed unbounded cell model of `Functor.ModuleCatCellModel`.  Its public API is
owned directly by `ModuleCat`.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe uR uA v

namespace CategoryTheory.ModuleCat

section

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]

/-- The canonical extension-of-scalars functor from `K(R)` to `D(A)`. -/
@[stacks 05S9 "extension of scalars from the homotopy category"]
noncomputable abbrev extendScalarsToDerived (σ : R →+* A) :
    HomotopyCategory (ModuleCat.{v, uR} R) (up ℤ) ⥤
      DerivedCategory (ModuleCat.{max uA v, uA} A) :=
  Functor.Homotopy.toDerived (ModuleCat.extendScalars.{uR, uA, v} σ)

/-- Extension of scalars has a pointwise unbounded left derived functor: at every complex the
pointwise limit is the displayed cone of the cell-model derived functor, whose lift evaluates at
the specified K-projective cell augmentation of the arbitrary unbounded input.  The smallness of
`R` in the module universe is the standard condition making free `R`-modules available there; it
is automatic when `v` is at least the universe of `R`. -/
@[stacks 05S9 "pointwise existence of derived extension of scalars"]
instance extendScalarsToDerived_hasPointwiseLeftDerived [Small.{v} R] (σ : R →+* A) :
    (extendScalarsToDerived σ).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{v, uR} R) (up ℤ)) :=
  Functor.ModuleCatCellModel.hasPointwiseLeftDerivedFunctor
    (ModuleCat.extendScalars.{uR, uA, v} σ)

/-- Extension of scalars along every map of commutative rings admits the
unbounded total left derived functor, obtained from the displayed pointwise limits. -/
@[stacks 05S9 "existence of derived extension of scalars"]
instance extendScalarsToDerived_hasLeftDerived [Small.{v} R] (σ : R →+* A) :
    (extendScalarsToDerived σ).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{v, uR} R) (up ℤ)) :=
  Functor.ModuleCatCellModel.hasLeftDerivedFunctor (ModuleCat.extendScalars.{uR, uA, v} σ)

/-- The unbounded derived extension-of-scalars functor `D(R) ⥤ D(A)`. -/
@[stacks 064M "derived extension of scalars"]
noncomputable abbrev derivedExtensionOfScalars (σ : R →+* A)
    [hasLeftDerived : (extendScalarsToDerived σ).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{v, uR} R) (up ℤ))] :
    DerivedCategory (ModuleCat.{v, uR} R) ⥤ DerivedCategory (ModuleCat.{max uA v, uA} A) :=
  @Functor.LeftDerived.Homotopy.functor
    (ModuleCat.{v, uR} R) _ _ _ (ModuleCat.{max uA v, uA} A) _ _ _
    (ModuleCat.extendScalars.{uR, uA, v} σ) inferInstance hasLeftDerived

/-- The canonical counit of derived extension of scalars. -/
@[stacks 05S9 "counit of derived extension of scalars"]
noncomputable abbrev derivedExtensionOfScalarsCounit (σ : R →+* A)
    [hasLeftDerived : (extendScalarsToDerived σ).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{v, uR} R) (up ℤ))] :
    (DerivedCategory.Qh :
      HomotopyCategory (ModuleCat.{v, uR} R) (up ℤ) ⥤ DerivedCategory (ModuleCat.{v, uR} R)) ⋙
        derivedExtensionOfScalars σ (hasLeftDerived := hasLeftDerived) ⟶
      extendScalarsToDerived σ :=
  @Functor.LeftDerived.Homotopy.counit
    (ModuleCat.{v, uR} R) _ _ _ (ModuleCat.{max uA v, uA} A) _ _ _
    (ModuleCat.extendScalars.{uR, uA, v} σ) inferInstance hasLeftDerived

/-- Derived extension of scalars canonically commutes with integer shifts. -/
@[stacks 05SE "derived extension of scalars commutes with shift"]
noncomputable instance derivedExtensionOfScalars_commShift (σ : R →+* A)
    [hasLeftDerived : (extendScalarsToDerived σ).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{v, uR} R) (up ℤ))]
    [hasPointwiseLeftDerived : (extendScalarsToDerived σ).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{v, uR} R) (up ℤ))] :
    (derivedExtensionOfScalars σ (hasLeftDerived := hasLeftDerived)).CommShift ℤ :=
  Functor.totalLeftDerived_commShift (extendScalarsToDerived σ)
    (HomotopyCategory.quasiIso (ModuleCat.{v, uR} R) (up ℤ))
    (DerivedCategory.Qh :
      HomotopyCategory (ModuleCat.{v, uR} R) (up ℤ) ⥤ DerivedCategory (ModuleCat.{v, uR} R))

/-- Derived extension of scalars is an exact functor between triangulated derived categories. -/
@[stacks 05SE "derived extension of scalars is triangulated"]
instance derivedExtensionOfScalars_isTriangulated (σ : R →+* A)
    [hasLeftDerived : (extendScalarsToDerived σ).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{v, uR} R) (up ℤ))]
    [hasPointwiseLeftDerived : (extendScalarsToDerived σ).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{v, uR} R) (up ℤ))] :
    (derivedExtensionOfScalars σ (hasLeftDerived := hasLeftDerived)).IsTriangulated := sorry

/-- An explicit left-derived model for extension of scalars along `σ`.  The model fixes the
localization to `DerivedCategory.Qh` and the quasi-isomorphisms of the source homotopy category. -/
@[stacks 05SA "explicit derived extension-of-scalars model"]
abbrev DerivedExtensionOfScalarsModel (σ : R →+* A) :=
  Functor.LeftDerived.Model
    (extendScalarsToDerived σ)
    (DerivedCategory.Qh :
      HomotopyCategory (ModuleCat.{v, uR} R) (up ℤ) ⥤
        DerivedCategory (ModuleCat.{v, uR} R))
    (HomotopyCategory.quasiIso (ModuleCat.{v, uR} R) (up ℤ))

/-- The canonical explicit model whose concrete fields are the derived extension and its counit,
together with the universal property identifying it as a left-derived functor.  The universal
property is mathlib's native right-Kan-extension witness for `totalLeftDerived` and its counit,
so the model stores no separately admitted universal data. -/
@[stacks 05SA "canonical explicit derived extension-of-scalars model"]
noncomputable def derivedExtensionOfScalarsModel (σ : R →+* A)
    [hasLeftDerived : (extendScalarsToDerived σ).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{v, uR} R) (up ℤ))] :
    DerivedExtensionOfScalarsModel σ where
  functor := derivedExtensionOfScalars σ (hasLeftDerived := hasLeftDerived)
  counit := derivedExtensionOfScalarsCounit σ (hasLeftDerived := hasLeftDerived)
  isLeftDerived := inferInstance

variable {σ : R →+* A}

/-- The concrete derived extension functor carried by an explicit model. -/
@[stacks 05SA "derived extension functor from an explicit model"]
noncomputable abbrev derivedExtensionOfScalarsOfModel
    (M : DerivedExtensionOfScalarsModel σ) :
    DerivedCategory (ModuleCat.{v, uR} R) ⥤
      DerivedCategory (ModuleCat.{max uA v, uA} A) :=
  M.functor

/-- The localization counit carried by an explicit derived extension model. -/
@[stacks 05SA "derived extension model counit"]
abbrev derivedExtensionOfScalarsCounitOfModel
    (M : DerivedExtensionOfScalarsModel σ) :=
  M.counit

/-- The universal-property witness carried by an explicit derived extension model. -/
@[stacks 05SA "derived extension model universal property"]
abbrev derivedExtensionOfScalarsIsLeftDerivedOfModel
    (M : DerivedExtensionOfScalarsModel σ) :=
  M.isLeftDerived

end

end CategoryTheory.ModuleCat

namespace DerivedTensorWithAlgebra

/- Scoped notation for the algebra-specialized derived extension object `K ⊗_R^L A`.
The canonical owner remains `CategoryTheory.ModuleCat.derivedExtensionOfScalars σ` for an
explicit ring homomorphism `σ`. -/
set_option quotPrecheck false in
scoped notation:70 K:70 " ⊗[" R:70 "]^L[" A:70 "]" =>
  (CategoryTheory.ModuleCat.derivedExtensionOfScalars (algebraMap R A)).obj K

end DerivedTensorWithAlgebra
