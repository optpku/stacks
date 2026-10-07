module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Naturality
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import stacks_project.Chap85.Lemma_85_33_3_Adjunction
public import stacks_project.Chap85.Lemma_85_33_4_Sections

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

/-- Inverse image along the spaces-étale augmentation sends a constant abelian
sheaf on `X_étale` to the corresponding constant sheaf on `U_étale`. -/
def constantSheafCompInverseImageHom :
    constantSheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ⋙
      inverseImage U AddCommGrpCat.{u + 1} a ⟶
    constantSheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1} where
  app M :=
    ((sheafLocalizationAdjunction a AddCommGrpCat.{u + 1}).homEquiv
        ((constantSheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}).obj M)
        ((constantSheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}).obj M)).symm
      (((sheafificationAdjunction (spacesEtaleTopology X) AddCommGrpCat.{u + 1}).homEquiv
          ((const _).obj M)
          ((directImage U AddCommGrpCat.{u + 1} a).obj
            ((constantSheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}).obj M))).symm
        ((constCompWhiskeringLeftIso (spacesEtaleSite X)ᵒᵖ
            (augmentationFunctor U a).op).inv.app M ≫
          whiskerLeft (augmentationFunctor U a).op
            ((sheafificationAdjunction (spacesEtaleTotalTopology U)
                AddCommGrpCat.{u + 1}).unit.app ((const _).obj M))))
  naturality := sorry

/-- Inverse image of constant abelian sheaves along the spaces-étale augmentation
is an isomorphism of functors. -/
instance constantSheafCompInverseImageHom_isIso :
    IsIso (constantSheafCompInverseImageHom a) :=
  sorry

/-- Inverse image along the spaces-étale augmentation preserves constant abelian
sheaves. -/
def constantSheafCompInverseImageIso :
    constantSheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ⋙
      inverseImage U AddCommGrpCat.{u + 1} a ≅
    constantSheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1} :=
  asIso (constantSheafCompInverseImageHom a)

/-- Underived identification `a_* ⋙ Γ(X_étale, -) ≅ Γ(U_étale, -)`. -/
def directImageCompGlobalSectionsIso :
    directImage U AddCommGrpCat.{u + 1} a ⋙
      Sheaf.Γ (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ≅
    Sheaf.Γ (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1} :=
  (((constantSheafΓAdj (spacesEtaleTopology X) AddCommGrpCat.{u + 1}).comp
        (sheafLocalizationAdjunction a AddCommGrpCat.{u + 1})).ofNatIsoLeft
      (constantSheafCompInverseImageIso a)).rightAdjointUniq
    (constantSheafΓAdj (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1})

/-- `directImageCompGlobalSectionsIso` is the right-adjoint uniqueness isomorphism of
`constantSheafΓAdj` after transporting `a⁻¹ ⊣ a_*` across constant sheaves. -/
theorem directImageCompGlobalSectionsIso_eq :
    directImageCompGlobalSectionsIso a =
      (((constantSheafΓAdj (spacesEtaleTopology X) AddCommGrpCat.{u + 1}).comp
            (sheafLocalizationAdjunction a AddCommGrpCat.{u + 1})).ofNatIsoLeft
          (constantSheafCompInverseImageIso a)).rightAdjointUniq
        (constantSheafΓAdj (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}) :=
  sorry

/-- Iterated bounded-below unit of `Ra_* ⋙ RΓ(X_étale, -)` as a right-derived model of
`a_* ⋙ Γ(X_étale, -)`. -/
def rGammaDirectImageUnit :
    (directImage U AddCommGrpCat.{u + 1} a ⋙
        Sheaf.Γ (spacesEtaleTopology X) AddCommGrpCat.{u + 1}).toBoundedBelowDerived ⟶
      DerivedCategory.Plus.Qh ⋙ (plusDirectImage a ⋙ plusGlobalSections X) :=
  (toBoundedBelowDerived.compIso
      (directImage U AddCommGrpCat.{u + 1} a)
      (Sheaf.Γ (spacesEtaleTopology X) AddCommGrpCat.{u + 1})).hom ≫
    RightDerived.Composition.iteratedUnit
      (RightDerived.Bounded.unit (directImage U AddCommGrpCat.{u + 1} a))
      (RightDerived.Bounded.unit
        (Sheaf.Γ (spacesEtaleTopology X) AddCommGrpCat.{u + 1}))

/-- The iterated model `Ra_* ⋙ RΓ(X_étale, -)` is a right-derived functor of
`a_* ⋙ Γ(X_étale, -)`. -/
instance rGammaDirectImage_isRightDerived :
    (plusDirectImage a ⋙ plusGlobalSections X).IsRightDerivedFunctor
      (rGammaDirectImageUnit a)
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1})) :=
  sorry

/-- `RΓ(U_étale, -)` is a right-derived functor of underived global sections on the
total spaces-étale site. -/
instance plusGlobalSectionsTotal_isRightDerived :
    (plusGlobalSectionsTotal U).IsRightDerivedFunctor
      (RightDerived.Bounded.unit
        (Sheaf.Γ (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}))
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1})) :=
  sorry

/-- Leray identification `Ra_* ⋙ RΓ(X_étale, -) ≅ RΓ(U_étale, -)` on `D⁺`. -/
def rGammaDirectImageIso :
    plusDirectImage a ⋙ plusGlobalSections X ≅ plusGlobalSectionsTotal U :=
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
  sorry

/-- Canonical comparison `RΓ(X_étale, -) ⟶ a⁻¹ ⋙ RΓ(U_étale, -)` on `D⁺`. -/
def rGammaInverseImageComparison :
    plusGlobalSections X ⟶ plusInverseImage a ⋙ plusGlobalSectionsTotal U :=
  whiskerRight (plusDerivedUnit a) (plusGlobalSections X) ≫
    (associator (plusInverseImage a) (plusDirectImage a) (plusGlobalSections X)).hom ≫
    whiskerLeft (plusInverseImage a) (rGammaDirectImageIso a).hom

/-- `rGammaInverseImageComparison` is the derived unit of `a⁻¹ ⊣ Ra_*`, reassociated and
postcomposed with the Leray identification `rGammaDirectImageIso`. -/
theorem rGammaInverseImageComparison_eq :
    rGammaInverseImageComparison a =
      whiskerRight (plusDerivedUnit a) (plusGlobalSections X) ≫
        (associator (plusInverseImage a) (plusDirectImage a)
            (plusGlobalSections X)).hom ≫
        whiskerLeft (plusInverseImage a) (rGammaDirectImageIso a).hom :=
  sorry

/-- The component of `rGammaInverseImageComparison` at `K` is
`RΓ(X_étale, K) ⟶ RΓ(U_étale, a⁻¹ K)`. -/
theorem rGammaInverseImageComparison_app
    (K : DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) :
    (rGammaInverseImageComparison a).app K =
      (plusGlobalSections X).map ((plusDerivedUnit a).app K) ≫
        (rGammaDirectImageIso a).hom.app ((plusInverseImage a).obj K) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
