/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.SingleFunctor
public import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution.Definition
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Homology.Below
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.KInjective.Bounded
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Total
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded and ordinary right-derived degrees

This leaf gives the concrete comparison between the canonical bounded-below degree functor and
Mathlib's ordinary injective-resolution right-derived functor.  The comparison is assembled from
the chosen injective resolution, the bounded-below computation isomorphism, and the explicit
integer-indexed resolution homology comparison.  It does not choose an isomorphism from a bare
`IsIsomorphic` proposition.
-/

open CategoryTheory ComplexShape

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.Functor.RightDerived.Bounded.degree

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasInjectiveResolutions A]
  (F : A ⥤ B) [F.Additive]
  [F.toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso A)]

/-- The chosen bounded-below injective resolution of an object, viewed as a
bounded-below termwise-injective cochain complex. -/
@[stacks 015A "injective-resolution representative for bounded degree comparison"]
noncomputable def resolutionPlus (X : A) : CochainComplex.InjectivePlus A :=
  ⟨⟨(injectiveResolution X).cochainComplex, ⟨0, inferInstance⟩⟩, fun _ => inferInstance⟩

/-- The comparison map from the single cochain complex to the chosen injective resolution. -/
@[stacks 015A "injective-resolution comparison cochain map"]
noncomputable def resolutionHom (X : A) :
    (CochainComplex.Plus.singleFunctor A 0).obj X ⟶ (resolutionPlus X).obj :=
  ObjectProperty.homMk (injectiveResolution X).ι'

/-- The comparison cochain map is a bounded-below quasi-isomorphism. -/
@[stacks 015A "injective-resolution comparison is a quasi-isomorphism"]
theorem resolutionHom_mem (X : A) :
    CochainComplex.Plus.quasiIso A (resolutionHom X) := sorry

/-- The comparison morphism after passage to the bounded-below homotopy category. -/
@[stacks 015A "injective-resolution comparison in the bounded homotopy category"]
noncomputable def resolutionHomotopy (X : A) :
    (HomotopyCategory.Plus.singleFunctor A 0).obj X ⟶
      (HomotopyCategory.Plus.quotient A).obj (resolutionPlus X).obj :=
  (CochainComplex.Plus.singleFunctorCompQuotientIso A 0).inv.app X ≫
    (HomotopyCategory.Plus.quotient A).map (resolutionHom X)

/-- The homotopy-category comparison is a quasi-isomorphism. -/
@[stacks 015A "injective-resolution homotopy comparison is a quasi-isomorphism"]
theorem resolutionHomotopy_mem (X : A) :
    HomotopyCategory.Plus.quasiIso A (resolutionHomotopy X) := sorry

/-- The bounded-derived value on the chosen injective resolution is canonically
identified with the canonical bounded-derived value on the single object. -/
@[stacks 015A "bounded-derived injective-resolution value comparison"]
noncomputable def resolutionValueIso (X : A) :
    F.toBoundedBelowDerived.obj
        ((HomotopyCategory.Plus.quotient A).obj (resolutionPlus X).obj) ≅
      (Functor.RightDerived.Bounded.functor F).obj
        ((DerivedCategory.Plus.singleFunctor A 0).obj X) :=
  Functor.RightDerived.ComputesAt.replacementIso
      F.toBoundedBelowDerived (HomotopyCategory.Plus.quasiIso A)
      (DerivedCategory.Plus.Qh : HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
      (resolutionHomotopy X) (resolutionHomotopy_mem X)
      (Functor.KInjective.Bounded.computesAtOfInjectivePlus
        F.toBoundedBelowDerived (resolutionPlus X)) ≪≫
    (F.toBoundedBelowDerived.totalRightDerived
      (DerivedCategory.Plus.Qh : HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
      (HomotopyCategory.Plus.quasiIso A)).mapIso
      ((DerivedCategory.Plus.singleFunctor.fromHomotopy.iso A 0).app X)

/-- The component comparison from a bounded-below degree to the ordinary
injective-resolution right-derived degree. -/
@[stacks 015A "bounded degree to ordinary right-derived component"]
noncomputable def degreeIsoRightDerived (n : ℕ) (X : A) :
    (DerivedCategory.Plus.homologyFunctor B (Int.ofNat n)).obj
        ((Functor.RightDerived.Bounded.functor F).obj
          ((DerivedCategory.Plus.singleFunctor A 0).obj X)) ≅
      (F.rightDerived n).obj X :=
  ((DerivedCategory.Plus.homologyFunctor B (Int.ofNat n)).mapIso
      (resolutionValueIso F X)).symm ≪≫
    (Functor.Homotopy.Plus.Homology.homologyIso F (resolutionPlus X).obj
      (Int.ofNat n)).symm ≪≫
    CategoryTheory.InjectiveResolution.RightDerived.homologyIso
      (injectiveResolution X) F n

/-- Naturality of the bounded-to-ordinary right-derived degree component. -/
@[reassoc, stacks 015A "naturality of the bounded-to-ordinary degree component"]
theorem degreeIsoRightDerived_hom_naturality {X Y : A} (f : X ⟶ Y) (n : ℕ) :
    (Functor.RightDerived.Bounded.degree F (Int.ofNat n)).map f ≫
        (degreeIsoRightDerived F n Y).hom =
      (degreeIsoRightDerived F n X).hom ≫ (F.rightDerived n).map f := sorry

/-- Stacks 015A: the bounded-below degree functor is canonically isomorphic to the ordinary
injective-resolution right-derived functor in every nonnegative degree. -/
@[stacks 015A "bounded and ordinary right-derived degree isomorphism"]
noncomputable def degreeFunctorIsoRightDerived (n : ℕ) :
    Functor.RightDerived.Bounded.degree F (Int.ofNat n) ≅ F.rightDerived n :=
  NatIso.ofComponents (fun X => degreeIsoRightDerived F n X)
    (fun f => degreeIsoRightDerived_hom_naturality F f n)

end CategoryTheory.Functor.RightDerived.Bounded.degree

end
