/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.SerreQuotient
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology
public import ReasLib.CategoryTheory.Pretriangulated.Functor.Localization
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived Functors of Serre Quotients

The quotient functor of a Serre class is exact, hence acts on cochain complexes and derived
categories.  This leaf owns the essential-surjectivity interfaces at both levels.  The complex
level is the primitive lifting statement; the derived level is its localization bridge.
-/

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.ObjectProperty.SerreClassLocalization
open ComplexShape

noncomputable section

universe wA wQ vA vQ uA

namespace CategoryTheory.ObjectProperty.SerreClassLocalization

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (P : ObjectProperty A) [P.IsSerreClass]

namespace Cochain.Quotient

/-- Stacks 06XL: the exact Serre quotient functor is essentially surjective on cochain complexes.
This is the primitive lifting interface used by the derived statement below. -/
@[stacks 06XL "Serre quotient complex lifting"]
noncomputable instance essSurj :
    (P.isoModSerre.Q.mapHomologicalComplex (ComplexShape.up ℤ)).EssSurj := sorry

end Cochain.Quotient

variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wQ} P.isoModSerre.Localization]

namespace Derived.Quotient

/-- Stacks 06XL: the functor on derived categories induced by a Serre quotient is essentially
surjective. -/
@[stacks 06XL "Serre quotient derived essential surjectivity"]
noncomputable instance essSurj :
    P.isoModSerre.Q.mapDerivedCategory.EssSurj := sorry

end Derived.Quotient

end CategoryTheory.ObjectProperty.SerreClassLocalization

namespace CategoryTheory.ObjectProperty.SerreClassLocalization.Derived.Quotient

open CategoryTheory.Limits

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (P : ObjectProperty A) [P.IsSerreClass]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wQ} P.isoModSerre.Localization]

/-- Taking degree-`i` homology after the derived Serre quotient is naturally
isomorphic to first taking homology and then applying the Serre quotient. -/
@[stacks 06XM "derived Serre quotient commutes naturally with homology"]
noncomputable abbrev homologyFunctorIso (i : ℤ) :
    P.isoModSerre.Q.mapDerivedCategory ⋙
        DerivedCategory.homologyFunctor P.isoModSerre.Localization i ≅
      DerivedCategory.homologyFunctor A i ⋙ P.isoModSerre.Q :=
  ExactFunctor.homologyFunctorIso
    (ObjectProperty.SerreClassLocalization.quotientExactFunctor P) i

/-- The objectwise component of the natural homology comparison for the
derived Serre quotient. -/
noncomputable abbrev homologyIso (X : DerivedCategory A) (i : ℤ) :
    (DerivedCategory.homologyFunctor P.isoModSerre.Localization i).obj
        (P.isoModSerre.Q.mapDerivedCategory.obj X) ≅
      P.isoModSerre.Q.obj ((DerivedCategory.homologyFunctor A i).obj X) :=
  (homologyFunctorIso P i).app X

/-- Forward naturality of the derived Serre quotient homology comparison. -/
@[reassoc (attr := simp), stacks 06XM "forward derived Serre homology naturality"]
theorem homologyIso_hom_naturality {X Y : DerivedCategory A}
    (f : X ⟶ Y) (i : ℤ) :
    (P.isoModSerre.Q.mapDerivedCategory ⋙
        DerivedCategory.homologyFunctor P.isoModSerre.Localization i).map f ≫
      (homologyIso P Y i).hom =
    (homologyIso P X i).hom ≫
      (DerivedCategory.homologyFunctor A i ⋙ P.isoModSerre.Q).map f := sorry

/-- Inverse naturality of the derived Serre quotient homology comparison. -/
@[reassoc (attr := simp), stacks 06XM "inverse derived Serre homology naturality"]
theorem homologyIso_inv_naturality {X Y : DerivedCategory A}
    (f : X ⟶ Y) (i : ℤ) :
    (DerivedCategory.homologyFunctor A i ⋙ P.isoModSerre.Q).map f ≫
      (homologyIso P Y i).inv =
    (homologyIso P X i).inv ≫
      (P.isoModSerre.Q.mapDerivedCategory ⋙
        DerivedCategory.homologyFunctor P.isoModSerre.Localization i).map f := sorry

/-- If an object becomes zero in the derived Serre quotient, then all of its cohomology objects
belong to the Serre class. -/
theorem mem_of_isZero {X : DerivedCategory A}
    (hX : IsZero (P.isoModSerre.Q.mapDerivedCategory.obj X)) :
    DerivedCategory.cohomologyIn P X := sorry

/-- The categorical kernel of the derived Serre quotient is the object property of complexes
whose cohomology belongs to the Serre class. -/
theorem kernel_eq :
    Functor.kernel P.isoModSerre.Q.mapDerivedCategory =
      DerivedCategory.cohomologyIn P := sorry

namespace Kernel

/-- A derived Serre quotient admitting a fully faithful left adjoint is a localization at the
cone-defined morphism property of its categorical kernel. -/
theorem isLocalization
    (u : P.isoModSerre.Localization ⥤ A)
    (adj : u ⊣ P.isoModSerre.Q) [u.Full] [u.Faithful] :
    P.isoModSerre.Q.mapDerivedCategory.IsLocalization
      (Functor.kernel P.isoModSerre.Q.mapDerivedCategory).trW := sorry

end Kernel

/-- Stacks 06XM: a derived Serre quotient admitting a fully faithful left adjoint is the
Verdier localization by the objects whose cohomology belongs to the Serre class. -/
@[stacks 06XM]
theorem isLocalization
    (u : P.isoModSerre.Localization ⥤ A)
    (adj : u ⊣ P.isoModSerre.Q) [u.Full] [u.Faithful] :
    P.isoModSerre.Q.mapDerivedCategory.IsLocalization
      (DerivedCategory.cohomologyIn P).trW := sorry

end CategoryTheory.ObjectProperty.SerreClassLocalization.Derived.Quotient
