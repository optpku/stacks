module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.IsConnected
public import ReasLib.CategoryTheory.Functor.Additive.Constant
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.Point
import Mathlib.Tactic.CrossRefAttribute

/-!
# Constant-colimit counits over a point

The counit of the constant-diagram/colimit adjunction is invertible for a connected indexing
category. Its derived analogue is invertible when the indexing category has an initial or
terminal object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe q q' u v w

namespace CategoryTheory.DerivedColimit

section Underived

variable {C : Type u} [Category.{v} C]
variable {A : Type w} [Category A]
variable [HasColimitsOfShape Cᵒᵖ A]

/-- The constant-diagram/colimit adjunction for `A`-valued presheaves on `C`. -/
@[stacks 08Q7 "constant-diagram colimit adjunction"]
abbrev constantColimitAdjunction :
    (colim : (Cᵒᵖ ⥤ A) ⥤ A) ⊣ (Functor.const (Cᵒᵖ) : A ⥤ Cᵒᵖ ⥤ A) :=
  Limits.colimConstAdj

/-- The counit of the constant-diagram/colimit adjunction is invertible for a connected index. -/
@[stacks 08Q7 "connected constant-colimit counit instance"]
instance constantColimitCounit_isIso [IsConnected C] :
    IsIso (constantColimitAdjunction (C := C) (A := A)).counit := sorry

/-- An initial or final object supplies the connectedness needed for the underived counit. -/
@[stacks 08Q7 "initial-or-final underived lower-shriek counit"]
theorem constantColimitCounit_isIso_of_hasInitial_or_hasTerminal
    (hC : Nonempty (Limits.HasInitial C) ∨ Nonempty (Limits.HasTerminal C)) :
    IsIso (constantColimitAdjunction (C := C) (A := A)).counit := sorry

end Underived

section Derived

variable {C : Type u} [Category.{v} C]
variable {A : Type w} [Category A] [Abelian A]
variable [HasDerivedCategory.{q'} A]
variable [HasDerivedCategory.{q} (Cᵒᵖ ⥤ A)]
variable [HasColimitsOfShape Cᵒᵖ A]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived C A :
    HomotopyCategory (Cᵒᵖ ⥤ A) (up ℤ) ⥤ DerivedCategory.{q'} A)
  (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (up ℤ))]

/-- The derived inverse image for the projection from `C` to a point. -/
@[stacks 08Q7 "derived constant inverse image"]
noncomputable abbrev derivedConstant :
    DerivedCategory.{q'} A ⥤ DerivedCategory.{q} (Cᵒᵖ ⥤ A) :=
  (Functor.const (Cᵒᵖ) : A ⥤ Cᵒᵖ ⥤ A).mapDerivedCategory

omit [HasColimitsOfShape Cᵒᵖ A] in
/-- The constant presheaf functor induces the canonical right-derived functor on derived
categories. -/
@[stacks 08Q7 "derived constant inverse-image right-derived owner"]
noncomputable instance derivedConstant_isRightDerivedFunctor :
    Functor.IsRightDerivedFunctor
      ((Functor.const (Cᵒᵖ) : A ⥤ Cᵒᵖ ⥤ A).mapDerivedCategory)
      ((Functor.const (Cᵒᵖ) : A ⥤ Cᵒᵖ ⥤ A).mapDerivedCategoryFactorsh.inv)
      (HomotopyCategory.quasiIso A (up ℤ)) := sorry

/-- The pointwise colimit owner supplies the canonical left-derived structure of `Lπ!`. -/
@[stacks 08Q7 "derived colimit left-derived owner"]
noncomputable instance derivedColimit_isLeftDerivedFunctor :
    Functor.IsLeftDerivedFunctor
      (categoryOverPointDerivedColimit C A)
      (Functor.totalLeftDerivedCounit
        (categoryOverPointColimitToDerived C A)
        (DerivedCategory.Qh :
          HomotopyCategory (Cᵒᵖ ⥤ A) (up ℤ) ⥤ DerivedCategory (Cᵒᵖ ⥤ A))
        (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (up ℤ)))
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (up ℤ)) := sorry

/-- The derived lower-shriek composite carries the right-derived structure needed for its
canonical counit. -/
@[stacks 08Q7 "derived constant-colimit right-derived owner"]
noncomputable instance derivedConstant_comp_derivedColimit_isRightDerivedFunctor :
    Functor.IsRightDerivedFunctor
      (derivedConstant (C := C) (A := A) ⋙ categoryOverPointDerivedColimit C A)
      (Functor.whiskerRight
          ((Functor.const (Cᵒᵖ) : A ⥤ Cᵒᵖ ⥤ A).mapDerivedCategoryFactorsh.inv)
          (categoryOverPointDerivedColimit C A) ≫
        (Functor.associator
          (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)
          ((Functor.const (Cᵒᵖ) : A ⥤ Cᵒᵖ ⥤ A).mapDerivedCategory)
          (categoryOverPointDerivedColimit C A)).hom)
      (HomotopyCategory.quasiIso A (up ℤ)) := sorry

/-- The canonical derived counit `π⁻¹ ⋙ Lπ! ⟶ 𝟭` for the projection to a point. -/
@[stacks 08Q7 "derived constant-colimit counit"]
noncomputable abbrev derivedColimitCounit :
    derivedConstant (C := C) (A := A) ⋙ categoryOverPointDerivedColimit C A ⟶
      𝟭 (DerivedCategory.{q'} A) :=
  Adjunction.derivedε
    (Adjunction.mapHomotopyCategoryAdjunction
      (constantColimitAdjunction (C := C) (A := A)))
    (HomotopyCategory.quasiIso A (up ℤ))
    (Functor.totalLeftDerivedCounit
      (categoryOverPointColimitToDerived C A)
      (DerivedCategory.Qh :
        HomotopyCategory (Cᵒᵖ ⥤ A) (up ℤ) ⥤ DerivedCategory (Cᵒᵖ ⥤ A))
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (up ℤ)))
    ((Functor.const (Cᵒᵖ) : A ⥤ Cᵒᵖ ⥤ A).mapDerivedCategoryFactorsh.inv)

/-- An initial or final object gives an invertible derived lower-shriek counit with coefficients
in any abelian category. -/
@[stacks 08Q7 "coefficient-general initial-or-final derived lower-shriek counit"]
theorem derivedColimitCounit_isIso_of_hasInitial_or_hasTerminal
    (hC : Nonempty (Limits.HasInitial C) ∨ Nonempty (Limits.HasTerminal C)) :
    IsIso (derivedColimitCounit (C := C) (A := A)) := sorry

end Derived

section SourceSpecializations

variable {C : Type u} [Category.{v} C]

section AbelianGroups

variable [HasDerivedCategory.{q'} AddCommGrpCat]
variable [HasDerivedCategory.{q} (Cᵒᵖ ⥤ AddCommGrpCat)]
variable [HasColimitsOfShape Cᵒᵖ AddCommGrpCat]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived C AddCommGrpCat :
    HomotopyCategory (Cᵒᵖ ⥤ AddCommGrpCat) (up ℤ) ⥤
      DerivedCategory.{q'} AddCommGrpCat)
  (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ AddCommGrpCat) (up ℤ))]

/-- If `C` has an initial or final object, then the derived
lower-shriek counit is invertible on the derived category of abelian groups. -/
@[stacks 08Q7 "abelian initial-or-final derived lower-shriek counit"]
theorem derivedColimitCounit_isIso_of_hasInitial_or_hasTerminal_abelian
    (hC : Nonempty (Limits.HasInitial C) ∨ Nonempty (Limits.HasTerminal C)) :
    IsIso (derivedColimitCounit (C := C) (A := AddCommGrpCat)) := sorry

end AbelianGroups

section Modules

variable {B : Type w} [Ring B]
variable [HasDerivedCategory.{q'} (ModuleCat B)]
variable [HasDerivedCategory.{q} (Cᵒᵖ ⥤ ModuleCat B)]
variable [HasColimitsOfShape Cᵒᵖ (ModuleCat B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived C (ModuleCat B) :
    HomotopyCategory (Cᵒᵖ ⥤ ModuleCat B) (up ℤ) ⥤
      DerivedCategory.{q'} (ModuleCat B))
  (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ ModuleCat B) (up ℤ))]

/-- For a ring `B`, if `C` has an initial or final object, then the
derived lower-shriek counit is invertible on the derived category of `B`-modules. -/
@[stacks 08Q7 "module initial-or-final derived lower-shriek counit"]
theorem derivedColimitCounit_isIso_of_hasInitial_or_hasTerminal_module
    (hC : Nonempty (Limits.HasInitial C) ∨ Nonempty (Limits.HasTerminal C)) :
    IsIso (derivedColimitCounit (C := C) (A := ModuleCat B)) := sorry

end Modules

end SourceSpecializations

end CategoryTheory.DerivedColimit
