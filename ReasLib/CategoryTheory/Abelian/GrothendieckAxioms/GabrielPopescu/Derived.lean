/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.Abelian.GrothendieckAxioms.GabrielPopescu
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.Functor.Derived.Exact.Cochain
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived Gabriel-Popescu embedding

The exact Gabriel-Popescu left adjoint induces a functor on derived categories. Its
right adjoint is the K-injective total right derived functor of the canonical module
embedding. This file owns the resulting adjunction and its full-faithfulness API.
-/

open CategoryTheory Limits ComplexShape

noncomputable section

universe w v u

namespace CategoryTheory.IsGrothendieckAbelian.GabrielPopescu.Derived

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]

/-- The module category associated to the distinguished separator of `C`. -/
@[stacks 0F5V "module category"]
abbrev Modules := ModuleCat (End (separator C))ᵐᵒᵖ

variable [HasDerivedCategory.{w} C]

/-- The exact Gabriel-Popescu functor on derived categories. -/
@[stacks 0F5V "left derived functor"]
noncomputable abbrev left : DerivedCategory (Modules C) ⥤ DerivedCategory C :=
  (tensorObj (separator C)).mapDerivedCategory

/-- The K-injective total right derived Gabriel-Popescu embedding. -/
@[stacks 0F5V "right derived functor"]
noncomputable abbrev right : DerivedCategory C ⥤ DerivedCategory (Modules C) :=
  Functor.RightDerived.KInjective.functor (preadditiveCoyonedaObj (separator C))

/-- The Gabriel-Popescu left adjoint applied degreewise to cochain complexes. -/
@[stacks 0F5V "left adjoint on complexes"]
abbrev complexLeft : CochainComplex (Modules C) ℤ ⥤ CochainComplex C ℤ :=
  (tensorObj (separator C)).mapHomologicalComplex (up ℤ)

/-- The Gabriel-Popescu embedding applied degreewise to cochain complexes. -/
@[stacks 0F5V "right adjoint on complexes"]
abbrev complexRight : CochainComplex C ℤ ⥤ CochainComplex (Modules C) ℤ :=
  (preadditiveCoyonedaObj (separator C)).mapHomologicalComplex (up ℤ)

/-- The Gabriel-Popescu adjunction lifted degreewise to cochain complexes. -/
@[stacks 0F5V "adjunction on complexes"]
noncomputable def complexAdjunction : complexLeft C ⊣ complexRight C :=
  Adjunction.mapHomologicalComplexAdjunction
    (tensorObjPreadditiveCoyonedaObjAdjunction (separator C)) (up ℤ)

/-- The comparison exhibiting `left C` as the cochain-level left derived functor. -/
@[stacks 0F5V "left derived comparison"]
noncomputable abbrev leftComparison :
    (DerivedCategory.Q : CochainComplex (Modules C) ℤ ⥤ DerivedCategory (Modules C)) ⋙
        left C ⟶
      complexLeft C ⋙ (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C) :=
  (tensorObj (separator C)).mapDerivedCategoryFactors.hom

/-- The comparison exhibiting `right C` as the K-injective right derived functor. -/
@[stacks 0F5V "right derived comparison"]
noncomputable abbrev rightComparison :
    complexRight C ⋙
        (DerivedCategory.Q : CochainComplex (Modules C) ℤ ⥤ DerivedCategory (Modules C)) ⟶
      (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C) ⋙ right C :=
  Functor.RightDerived.KInjective.unit (preadditiveCoyonedaObj (separator C))

/-- The comparison for the composite of the left and right derived Gabriel-Popescu functors. -/
@[stacks 0F5V "left-right derived comparison"]
noncomputable abbrev leftRightComparison :
    (DerivedCategory.Q : CochainComplex (Modules C) ℤ ⥤ DerivedCategory (Modules C)) ⋙
        (left C ⋙ right C) ⟶
      (complexLeft C ⋙
          (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C)) ⋙ right C :=
  (Functor.associator
      (DerivedCategory.Q : CochainComplex (Modules C) ℤ ⥤ DerivedCategory (Modules C))
      (left C) (right C)).inv ≫
    Functor.whiskerRight (leftComparison C) (right C)

/-- The comparison for the composite of the right and left derived Gabriel-Popescu functors. -/
@[stacks 0F5V "right-left derived comparison"]
noncomputable abbrev rightLeftComparison :
    (complexRight C ⋙
        (DerivedCategory.Q : CochainComplex (Modules C) ℤ ⥤ DerivedCategory (Modules C))) ⋙
        left C ⟶
      (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C) ⋙
        (right C ⋙ left C) :=
  Functor.whiskerRight (rightComparison C) (left C) ≫
    (Functor.associator
      (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C)
      (right C) (left C)).hom

/-- The exact Gabriel-Popescu lift satisfies the left-derived universal property. -/
@[stacks 0F5V "left derived universal property"]
noncomputable instance leftIsDerived :
    (left C).IsLeftDerivedFunctor (leftComparison C)
      (HomologicalComplex.quasiIso (Modules C) (up ℤ)) := sorry

/-- The K-injective Gabriel-Popescu lift satisfies the right-derived universal property. -/
@[stacks 0F5V "right derived universal property"]
noncomputable instance rightIsDerived :
    (right C).IsRightDerivedFunctor (rightComparison C)
      (HomologicalComplex.quasiIso C (up ℤ)) := sorry

/-- The composite of the two derived models has the left-derived universal property needed
to derive the Gabriel-Popescu adjunction. -/
@[stacks 0F5V "left-right derived universal property"]
noncomputable instance leftRightIsDerived :
    (left C ⋙ right C).IsLeftDerivedFunctor
      (leftRightComparison C)
      (HomologicalComplex.quasiIso (Modules C) (up ℤ)) := sorry

/-- The reverse composite has the right-derived universal property needed to derive the
Gabriel-Popescu adjunction. -/
@[stacks 0F5V "right-left derived universal property"]
noncomputable instance rightLeftIsDerived :
    (right C ⋙ left C).IsRightDerivedFunctor
      (rightLeftComparison C)
      (HomologicalComplex.quasiIso C (up ℤ)) := sorry

/-- Lemma 19.14.4: the derived Gabriel-Popescu functor is left adjoint to the
K-injective right derived embedding. -/
@[stacks 0F5V "derived adjunction"]
noncomputable def adjunction : left C ⊣ right C :=
  Adjunction.derived (complexAdjunction C)
    (HomologicalComplex.quasiIso (Modules C) (up ℤ))
    (HomologicalComplex.quasiIso C (up ℤ))
    (leftComparison C) (rightComparison C)

/-- The counit of the derived Gabriel-Popescu adjunction is invertible. Equivalently,
`right C ⋙ left C` is canonically isomorphic to the identity. -/
@[stacks 0F5V "derived counit"]
noncomputable instance counitIsIso : IsIso (adjunction C).counit := sorry

/-- The derived Gabriel-Popescu embedding is full. -/
@[stacks 0F5V "derived fullness"]
noncomputable instance rightFull : (right C).Full := sorry

/-- The derived Gabriel-Popescu embedding is faithful. -/
@[stacks 0F5V "derived faithfulness"]
noncomputable instance rightFaithful : (right C).Faithful := sorry

/-- The derived Gabriel-Popescu embedding induces a bijection on every hom-set. -/
@[stacks 0F5V "derived hom bijection"]
theorem map_bijective (X Y : DerivedCategory C) :
    Function.Bijective
      ((right C).map : (X ⟶ Y) → ((right C).obj X ⟶ (right C).obj Y)) := sorry

end CategoryTheory.IsGrothendieckAbelian.GabrielPopescu.Derived
