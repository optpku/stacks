module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Hom
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.RHom
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.KProjective
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.Localization
public import ReasLib.CategoryTheory.Shift.ShiftedHom.ModuleCat

/-!
# Cohomology of derived DG-module Hom

This leaf identifies degreewise cohomology of the derived DG-module `RHom` bifunctor with
shifted morphisms in the DG-module derived category.  The functorial statement is lifted to the
universe of derived morphisms; the pointwise `linearEquiv` hides that implementation detail.

The comparison is descended from property-(P) homotopy models.  No resolution or representative
choice appears in the public API, and the source/target naturality is carried by one bifunctorial
natural isomorphism.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedModule.Derived.RHom.Cohomology

variable {R : Type u} [CommRing R]

/- The ordinary functor is kept as a small helper; the public bifunctor uses `uliftFunctor` so
  that its codomain has the universe of derived-category morphisms. -/

/-- Degree-`n` cohomology of derived DG-module `RHom`, before the universe lift. -/
@[stacks 0CS6 "cohomology bifunctor of derived DG-module Hom"]
noncomputable abbrev functor (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :=
  DifferentialGradedModule.Derived.RHom.functor A ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{v} R) n

/-- Lifted degree-`n` cohomology of derived DG-module `RHom`. -/
@[stacks 0CS6 "lifted cohomology bifunctor of derived DG-module Hom"]
noncomputable abbrev uliftFunctor (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :=
  functor A n ⋙ ModuleCat.uliftFunctor.{max u (v + 1)} R

/-- The bifunctor of degree-`n` shifted morphisms in the DG-module derived category. -/
@[stacks 0CS6 "shifted-Hom bifunctor for derived DG modules"]
noncomputable abbrev shiftedFunctor (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :=
  Functor.uncurry.obj
    (ShiftedHom.linearCoyoneda R (DifferentialGradedModule.Derived.Category.{u, v} A) n)

namespace PropertyP

/-- Pairs of property-(P) homotopy objects used to compute derived `RHom` cohomology. -/
@[stacks 0CS6 "property-P domain for derived Hom cohomology"]
abbrev Domain (A : CochainDGAlgebra.{u, v} R) :=
  (DifferentialGradedModule.Homotopy.propertyP A).FullSubcategoryᵒᵖ ×
    (DifferentialGradedModule.Homotopy.propertyP A).FullSubcategory

/-- The product quasi-isomorphism system on property-(P) pairs. -/
@[stacks 0CS6 "property-P quasi-isomorphisms for derived Hom cohomology"]
abbrev qis (A : CochainDGAlgebra.{u, v} R) : MorphismProperty (Domain A) :=
  (DifferentialGradedModule.Homotopy.PropertyP.qis A).op.prod
    (DifferentialGradedModule.Homotopy.PropertyP.qis A)

/-- The product localization from property-(P) pairs to the DG-module derived category. -/
@[stacks 0CS6 "property-P localization for derived Hom cohomology"]
noncomputable abbrev localization (A : CochainDGAlgebra.{u, v} R) :=
  (DifferentialGradedModule.Homotopy.PropertyP.localization A).op.prod
    (DifferentialGradedModule.Homotopy.PropertyP.localization A)

/-- The property-(P) comparison from cohomology of strict Hom to shifted derived morphisms. -/
@[stacks 0CS6 "property-P cohomology-to-Ext comparison"]
noncomputable def appIso (A : CochainDGAlgebra.{u, v} R) (n : ℤ)
    (X : Domain A) :
    (localization A ⋙ uliftFunctor A n).obj X ≅
      (localization A ⋙ shiftedFunctor A n).obj X :=
  (ModuleCat.uliftFunctor.{max u (v + 1)} R).mapIso
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).mapIso
          (DifferentialGradedModule.Derived.RHom.unitAppIsoOfPropertyP
            A X.1.unop.obj.obj X.2.obj.obj X.1.unop.property).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) n).app
          (homComplex X.1.unop.obj.obj X.2.obj.obj)) ≪≫
    ((ULift.moduleEquiv.{u, v, max u (v + 1)} (R := R)
        (M := (homComplex X.1.unop.obj.obj X.2.obj.obj).homology n)).trans
      (DifferentialGradedModule.Derived.homologyHomLinearEquiv
        X.1.unop.obj.obj X.2.obj.obj n X.1.unop.property.kProjective)).toModuleIso

/-- The property-(P) comparison is natural in both DG-module variables. -/
theorem appIso_naturality (A : CochainDGAlgebra.{u, v} R) (n : ℤ)
    {X Y : Domain A} (f : X ⟶ Y) :
    (localization A ⋙ uliftFunctor A n).map f ≫ (appIso A n Y).hom =
      (appIso A n X).hom ≫ (localization A ⋙ shiftedFunctor A n).map f := sorry

/-- The property-(P) comparisons form a bifunctorial natural isomorphism. -/
@[stacks 0CS6 "property-P derived Hom cohomology isomorphism"]
noncomputable def iso (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    localization A ⋙ uliftFunctor A n ≅ localization A ⋙ shiftedFunctor A n :=
  NatIso.ofComponents (fun X ↦ appIso A n X) (fun {_ _} f ↦ appIso_naturality A n f)

/-- The component of the property-(P) comparison isomorphism at a model pair. -/
@[simp]
theorem iso_app (A : CochainDGAlgebra.{u, v} R) (n : ℤ)
    (X : Domain A) :
    (iso A n).app X = appIso A n X := sorry

namespace Source

/-- Pairs with property-(P) source and arbitrary DG homotopy target. -/
@[stacks 0CS6 "one-sided property-P domain for derived Hom cohomology"]
abbrev Domain (A : CochainDGAlgebra.{u, v} R) :=
  (DifferentialGradedModule.Homotopy.propertyP A).FullSubcategoryᵒᵖ ×
    K R (DifferentialGradedModule.{u, v} A)

/-- Quasi-isomorphisms for the one-sided property-(P) model. -/
@[stacks 0CS6 "one-sided property-P quasi-isomorphisms for derived Hom"]
abbrev qis (A : CochainDGAlgebra.{u, v} R) : MorphismProperty (Domain A) :=
  (DifferentialGradedModule.Homotopy.PropertyP.qis A).op.prod
    (DifferentialGradedModule.quasiIso A)

/-- The one-sided localization from property-(P) source models and arbitrary targets to derived
DG modules. -/
@[stacks 0CS6 "one-sided property-P localization for derived Hom"]
noncomputable abbrev localization (A : CochainDGAlgebra.{u, v} R) :
    Domain A ⥤
      (DifferentialGradedModule.Derived.Category.{u, v} A)ᵒᵖ ×
        DifferentialGradedModule.Derived.Category.{u, v} A :=
  (DifferentialGradedModule.Homotopy.PropertyP.localization A).op.prod
    (DifferentialGradedModule.Derived.Q A)

/-- The one-sided strict-model comparison for derived Hom cohomology. -/
@[stacks 0CS6 "one-sided property-P cohomology-to-Ext comparison"]
noncomputable def appIso (A : CochainDGAlgebra.{u, v} R) (n : ℤ)
    (X : Domain A) :
    (localization A ⋙ uliftFunctor A n).obj X ≅
      (localization A ⋙ shiftedFunctor A n).obj X :=
  (ModuleCat.uliftFunctor.{max u (v + 1)} R).mapIso
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).mapIso
          (DifferentialGradedModule.Derived.RHom.unitAppIsoOfPropertyP
            A X.1.unop.obj.obj X.2 X.1.unop.property).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) n).app
          (DifferentialGradedCategory.homComplex X.1.unop.obj.obj X.2)) ≪≫
    ((ULift.moduleEquiv.{u, v, max u (v + 1)} (R := R)
        (M := (DifferentialGradedCategory.homComplex X.1.unop.obj.obj X.2).homology n)).trans
      (DifferentialGradedModule.Derived.homologyHomLinearEquiv
        X.1.unop.obj.obj X.2 n X.1.unop.property.kProjective)).toModuleIso

/-- The one-sided comparison is natural in the source and target variables. -/
@[reassoc, stacks 0CS6 "one-sided property-P comparison naturality"]
theorem appIso_naturality (A : CochainDGAlgebra.{u, v} R) (n : ℤ)
    {X Y : Domain A} (f : X ⟶ Y) :
    (localization A ⋙ uliftFunctor A n).map f ≫ (appIso A n Y).hom =
      (appIso A n X).hom ≫ (localization A ⋙ shiftedFunctor A n).map f := sorry

/-- The one-sided comparisons form a natural isomorphism on the model localization. -/
@[stacks 0CS6 "one-sided property-P derived Hom cohomology isomorphism"]
noncomputable def iso (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    localization A ⋙ uliftFunctor A n ≅ localization A ⋙ shiftedFunctor A n :=
  NatIso.ofComponents (fun X ↦ appIso A n X)
    (fun {_ _} f ↦ appIso_naturality A n f)

/-- The one-sided comparison descends to arbitrary derived DG-module pairs. -/
@[stacks 0CS6 "one-sided property-P derived Hom cohomology representation"]
noncomputable def derivedIso (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    uliftFunctor A n ≅ shiftedFunctor A n :=
  Localization.liftNatIso (localization A) (qis A)
    (localization A ⋙ uliftFunctor A n)
    (localization A ⋙ shiftedFunctor A n)
    (uliftFunctor A n) (shiftedFunctor A n) (iso A n)

variable (A : CochainDGAlgebra.{u, v} R)

#synth (localization A).IsLocalization (qis A)

end Source
end PropertyP

/-- Degreewise cohomology of derived `RHom` is naturally represented by shifted derived Hom. -/
@[stacks 0CS6 "derived DG-module Hom cohomology representation"]
noncomputable def iso (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    uliftFunctor A n ≅ shiftedFunctor A n :=
  PropertyP.Source.derivedIso A n

/-- The ordinary (unlifted) cohomology-to-Ext linear equivalence. -/
@[stacks 0CS6 "derived DG-module cohomology as Ext"]
noncomputable def linearEquiv (A : CochainDGAlgebra.{u, v} R)
    (M N : DifferentialGradedModule.Derived.Category.{u, v} A) (n : ℤ) :
    (functor A n).obj (Opposite.op M, N) ≃ₗ[R]
      ShiftedHom M N n :=
  (ULift.moduleEquiv.{u, v, max u (v + 1)} (R := R)
      (M := (functor A n).obj (Opposite.op M, N))).symm.trans
    ((iso A n).app (Opposite.op M, N)).toLinearEquiv

/-- The forward map of the ordinary cohomology-to-Ext equivalence is the lifted comparison. -/
@[simp]
theorem linearEquiv_apply (A : CochainDGAlgebra.{u, v} R)
    (M N : DifferentialGradedModule.Derived.Category.{u, v} A) (n : ℤ)
    (x : (functor A n).obj (Opposite.op M, N)) :
    linearEquiv A M N n x =
      (iso A n).hom.app (Opposite.op M, N)
        (ULift.up x) := sorry

/-- The lifted cohomology representation is natural in both derived variables. -/
@[reassoc, stacks 0CS6 "derived DG-module Hom cohomology naturality"]
theorem iso_naturality (A : CochainDGAlgebra.{u, v} R) (n : ℤ)
    {X Y : (DifferentialGradedModule.Derived.Category.{u, v} A)ᵒᵖ ×
      DifferentialGradedModule.Derived.Category.{u, v} A} (f : X ⟶ Y) :
    (uliftFunctor A n).map f ≫ (iso A n).hom.app Y =
      (iso A n).hom.app X ≫ (shiftedFunctor A n).map f := sorry

end DifferentialGradedModule.Derived.RHom.Cohomology
