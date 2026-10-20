module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor.Bifunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.StructureSheaf

/-! # The left unit map for derived tensor of étale modules -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}}

/-- The derived tensor bifunctor computed by functorial cell replacements of both factors. -/
def tensorBifunctor (X : AlgebraicSpace S) :
    ModuleDerived X × ModuleDerived X ⥤ ModuleDerived X :=
  Modules.CellTensor.derived X

/-- The canonical map from the derived tensor of the degree-zero structure sheaf with a
derived module to that module, induced by the cell-model counit and the cochain left unitor. -/
def tensorLeftUnitor {X : AlgebraicSpace S} (K : ModuleDerived X) :
    (tensorBifunctor X).obj ((DerivedQCoh.structureSheaf X).obj, K) ⟶ K :=
  (tensorBifunctor X).map
      (Prod.mkHom (𝟙 (DerivedQCoh.structureSheaf X).obj)
        (DerivedCategory.Q.objObjPreimageIso K).inv) ≫
    (tensorBifunctor X).map
      (Prod.mkHom
        ((DerivedCategory.quotientCompQhIso X.Modules).inv.app
          (tensorUnit (CochainComplex X.Modules ℤ)))
        ((DerivedCategory.quotientCompQhIso X.Modules).inv.app
          (DerivedCategory.Q.objPreimage K))) ≫
    (Modules.CellTensor.model X).counit.app
      ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj
          (tensorUnit (CochainComplex X.Modules ℤ)),
        (HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj
          (DerivedCategory.Q.objPreimage K)) ≫
    (DerivedTensor.Bifunctor.sourceFunctorObjIso
      (tensorUnit (CochainComplex X.Modules ℤ)) (DerivedCategory.Q.objPreimage K)).hom ≫
    DerivedCategory.Q.map (leftUnitor (DerivedCategory.Q.objPreimage K)).hom ≫
    (DerivedCategory.Q.objObjPreimageIso K).hom

/-- The left unit map is the cell-model counit followed by the localized cochain left unitor,
transported along the canonical comparisons for the chosen complex representative. -/
theorem tensorLeftUnitor_eq {X : AlgebraicSpace S} (K : ModuleDerived X) :
    tensorLeftUnitor K =
      (tensorBifunctor X).map
          (Prod.mkHom (𝟙 (DerivedQCoh.structureSheaf X).obj)
            (DerivedCategory.Q.objObjPreimageIso K).inv) ≫
        (tensorBifunctor X).map
          (Prod.mkHom
            ((DerivedCategory.quotientCompQhIso X.Modules).inv.app
              (tensorUnit (CochainComplex X.Modules ℤ)))
            ((DerivedCategory.quotientCompQhIso X.Modules).inv.app
              (DerivedCategory.Q.objPreimage K))) ≫
        (Modules.CellTensor.model X).counit.app
          ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj
              (tensorUnit (CochainComplex X.Modules ℤ)),
            (HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj
              (DerivedCategory.Q.objPreimage K)) ≫
        (DerivedTensor.Bifunctor.sourceFunctorObjIso
          (tensorUnit (CochainComplex X.Modules ℤ)) (DerivedCategory.Q.objPreimage K)).hom ≫
        DerivedCategory.Q.map (leftUnitor (DerivedCategory.Q.objPreimage K)).hom ≫
        (DerivedCategory.Q.objObjPreimageIso K).hom :=
  rfl

/-- Derived tensor with the degree-zero structure sheaf has an invertible canonical left
unit map. -/
instance tensorLeftUnitor_isIso {X : AlgebraicSpace S} (K : ModuleDerived X) :
    IsIso (tensorLeftUnitor K) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
