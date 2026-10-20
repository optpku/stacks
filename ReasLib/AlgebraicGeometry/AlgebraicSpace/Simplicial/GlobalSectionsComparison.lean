module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Naturality
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleDerived
public import ReasLib.CategoryTheory.Sites.GlobalSections.AbelianToposMorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.GlobalSections

/-!
# Derived global-sections comparison for a spaces-étale augmentation

For an augmentation `a : U ⟶ X`, inverse image of constant abelian sheaves is
constant, so `a_* ⋙ Γ_X ≅ Γ_U` by uniqueness of right adjoints. This Leray
identification transports to `D⁺`, and the canonical comparison
`RΓ(X_étale, -) ⟶ a⁻¹ ⋙ RΓ(U_étale, -)` is the derived unit of `a⁻¹ ⊣ Ra_*`
followed by that identification.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open Functor
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Underived abelian direct image of total étale augmentation commutes with
global sections. -/
def directImageCompGlobalSectionsIso :
    (spacesEtaleAugmentation U a).abelianDirectImage ⋙
      Sheaf.Γ (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ≅
    Sheaf.Γ (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1} :=
  (spacesEtaleAugmentation U a).abelianPushforwardCompΓIso

/-- The abelian global-sections comparison is the specialization of the
canonical comparison for a morphism of topoi. -/
theorem directImageCompGlobalSectionsIso_eq :
    directImageCompGlobalSectionsIso a =
      (spacesEtaleAugmentation U a).abelianPushforwardCompΓIso := rfl

/-- Inverse image of total étale augmentation preserves constant abelian sheaves. -/
def constantSheafCompInverseImageIso :
    constantSheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ⋙
      (spacesEtaleAugmentation U a).abelianInverseImage ≅
    constantSheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1} :=
  Adjunction.leftAdjointUniq
    (((constantSheafΓAdj (spacesEtaleTopology X) AddCommGrpCat.{u + 1}).comp
        (spacesEtaleAugmentation U a).abelianAdjunction).ofNatIsoRight
      (directImageCompGlobalSectionsIso a))
    (constantSheafΓAdj (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1})

/-- The canonical map from the inverse image of a constant abelian sheaf to
the corresponding constant abelian sheaf on the total étale site. -/
def constantSheafCompInverseImageHom :
    constantSheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ⋙
      (spacesEtaleAugmentation U a).abelianInverseImage ⟶
    constantSheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1} :=
  (constantSheafCompInverseImageIso a).hom

/-- The canonical constant-sheaf comparison for total étale augmentation is invertible. -/
instance constantSheafCompInverseImageHom_isIso :
    IsIso (constantSheafCompInverseImageHom a) :=
  inferInstanceAs (IsIso (constantSheafCompInverseImageIso a).hom)

/-- Iterated bounded-below unit of `Ra_* ⋙ RΓ(X_étale, -)` as a right-derived model of
`a_* ⋙ Γ(X_étale, -)`. -/
def rGammaDirectImageUnit :
    ((spacesEtaleAugmentation U a).abelianDirectImage ⋙
        Sheaf.Γ (spacesEtaleTopology X) AddCommGrpCat.{u + 1}).toBoundedBelowDerived ⟶
      DerivedCategory.Plus.Qh ⋙ (EtaleDerived.plusDirectImage a ⋙ plusGlobalSections X) :=
  (toBoundedBelowDerived.compIso
      ((spacesEtaleAugmentation U a).abelianDirectImage)
      (Sheaf.Γ (spacesEtaleTopology X) AddCommGrpCat.{u + 1})).hom ≫
    RightDerived.Composition.iteratedUnit
      (RightDerived.Bounded.unit ((spacesEtaleAugmentation U a).abelianDirectImage))
      (RightDerived.Bounded.unit
        (Sheaf.Γ (spacesEtaleTopology X) AddCommGrpCat.{u + 1}))

/-- The iterated model `Ra_* ⋙ RΓ(X_étale, -)` is a right-derived functor of
`a_* ⋙ Γ(X_étale, -)`. -/
instance rGammaDirectImage_isRightDerived :
    (EtaleDerived.plusDirectImage a ⋙ plusGlobalSections X).IsRightDerivedFunctor
      (rGammaDirectImageUnit a)
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1})) :=
  sorry

/-- `RΓ(U_étale, -)` is a right-derived functor of underived global sections on the
total spaces-étale site. -/
instance plusGlobalSectionsTotal_isRightDerived :
    (plusGlobalSectionsTotal U).IsRightDerivedFunctor
      ((Sheaf.Γ (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}).toBoundedBelowDerived.totalRightDerivedUnit
        DerivedCategory.Plus.Qh
        (HomotopyCategory.Plus.quasiIso
          (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1})))
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1})) :=
  inferInstanceAs
    (((Sheaf.Γ (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}).toBoundedBelowDerived.totalRightDerived
      DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}))).IsRightDerivedFunctor
      ((Sheaf.Γ (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}).toBoundedBelowDerived.totalRightDerivedUnit
        DerivedCategory.Plus.Qh
        (HomotopyCategory.Plus.quasiIso
          (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1})))
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1})))

/-- Leray identification `Ra_* ⋙ RΓ(X_étale, -) ≅ RΓ(U_étale, -)` on `D⁺`. -/
def rGammaDirectImageIso :
    EtaleDerived.plusDirectImage a ⋙ plusGlobalSections X ≅ plusGlobalSectionsTotal U :=
  RightDerived.natIsoOfIso DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}))
    (rGammaDirectImageUnit a)
    (RightDerived.Bounded.unit
      (Sheaf.Γ (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}))
    (NatIso.toBoundedBelowDerived (directImageCompGlobalSectionsIso a))

/-- `rGammaDirectImageIso` is `RightDerived.natIsoOfIso` of
`directImageCompGlobalSectionsIso`. -/
theorem rGammaDirectImageIso_eq :
    rGammaDirectImageIso a =
      RightDerived.natIsoOfIso DerivedCategory.Plus.Qh
        (HomotopyCategory.Plus.quasiIso
          (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}))
        (rGammaDirectImageUnit a)
        (RightDerived.Bounded.unit
          (Sheaf.Γ (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}))
        (NatIso.toBoundedBelowDerived (directImageCompGlobalSectionsIso a)) :=
  rfl

/-- Canonical comparison `RΓ(X_étale, -) ⟶ a⁻¹ ⋙ RΓ(U_étale, -)` on `D⁺`. -/
def rGammaInverseImageComparison :
    plusGlobalSections X ⟶ EtaleDerived.plusInverseImage a ⋙ plusGlobalSectionsTotal U :=
  whiskerRight (EtaleDerived.plusDerivedUnit a) (plusGlobalSections X) ≫
    (associator (EtaleDerived.plusInverseImage a) (EtaleDerived.plusDirectImage a) (plusGlobalSections X)).hom ≫
    whiskerLeft (EtaleDerived.plusInverseImage a) (rGammaDirectImageIso a).hom

/-- `rGammaInverseImageComparison` is the derived unit of `a⁻¹ ⊣ Ra_*`, reassociated and
postcomposed with the Leray identification `rGammaDirectImageIso`. -/
theorem rGammaInverseImageComparison_eq :
    rGammaInverseImageComparison a =
      whiskerRight (EtaleDerived.plusDerivedUnit a) (plusGlobalSections X) ≫
        (associator (EtaleDerived.plusInverseImage a) (EtaleDerived.plusDirectImage a)
            (plusGlobalSections X)).hom ≫
        whiskerLeft (EtaleDerived.plusInverseImage a) (rGammaDirectImageIso a).hom :=
  rfl

/-- The component of `rGammaInverseImageComparison` at `K` is
`RΓ(X_étale, K) ⟶ RΓ(U_étale, a⁻¹ K)`. -/
theorem rGammaInverseImageComparison_app
    (K : DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) :
    (rGammaInverseImageComparison a).app K =
      (plusGlobalSections X).map ((EtaleDerived.plusDerivedUnit a).app K) ≫
        (rGammaDirectImageIso a).hom.app ((EtaleDerived.plusInverseImage a).obj K) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
