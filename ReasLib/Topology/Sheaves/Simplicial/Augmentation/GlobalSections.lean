/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Naturality
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import ReasLib.CategoryTheory.Sites.GlobalSections.Additive
public import ReasLib.Topology.Sheaves.Simplicial.Augmentation.Derived
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Restriction

/-!
# Derived global-sections comparison for a Zariski augmentation

For an augmentation `a : Y ⟶ constSpace X`, inverse image of constant abelian
sheaves is constant, so `a_* ⋙ Γ(X, -) ≅ Γ(Y_Zar, -)` by uniqueness of right
adjoints. This Leray identification transports to `D⁺`, and the canonical
comparison `RΓ(X, -) ⟶ a⁻¹ ⋙ RΓ(Y_Zar, -)` is the derived unit of `a⁻¹ ⊣ Ra_*`
followed by that identification.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopCat TopologicalSpace

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject

/-- Bounded-below derived global sections `RΓ(X, -)` on `D⁺`. -/
abbrev plusGlobalSections (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))] :
    DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ⥤
      DerivedCategory.Plus AddCommGrpCat.{u} :=
  Functor.RightDerived.Bounded.functor
    (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- `plusGlobalSections X` is the canonical bounded-below right-derived functor of
`Sheaf.Γ` on `Opens.grothendieckTopology X`. -/
theorem plusGlobalSections_eq (X : TopCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))] :
    plusGlobalSections X =
      Functor.RightDerived.Bounded.functor
        (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  rfl

/-- Bounded-below derived global sections `RΓ(Y_Zar, -)` on `D⁺`. -/
abbrev plusZariskiGlobalSections (Y : SimplicialObject TopCat.{u})
    [HasSheafify (zariskiTopology Y) AddCommGrpCat.{u}]
    [HasGlobalSectionsFunctor (zariskiTopology Y) AddCommGrpCat.{u}]
    [(Sheaf.Γ (zariskiTopology Y) AddCommGrpCat.{u}).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (zariskiTopology Y) AddCommGrpCat.{u}))] :
    DerivedCategory.Plus (Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) ⥤
      DerivedCategory.Plus AddCommGrpCat.{u} :=
  Functor.RightDerived.Bounded.functor
    (Sheaf.Γ (zariskiTopology Y) AddCommGrpCat.{u})

/-- `plusZariskiGlobalSections Y` is the canonical bounded-below right-derived functor of
`Sheaf.Γ` on `zariskiTopology Y`. -/
theorem plusZariskiGlobalSections_eq (Y : SimplicialObject TopCat.{u})
    [HasSheafify (zariskiTopology Y) AddCommGrpCat.{u}]
    [HasGlobalSectionsFunctor (zariskiTopology Y) AddCommGrpCat.{u}]
    [(Sheaf.Γ (zariskiTopology Y) AddCommGrpCat.{u}).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (zariskiTopology Y) AddCommGrpCat.{u}))] :
    plusZariskiGlobalSections Y =
      Functor.RightDerived.Bounded.functor
        (Sheaf.Γ (zariskiTopology Y) AddCommGrpCat.{u}) :=
  rfl

variable {Y : SimplicialObject TopCat.{u}} {X : TopCat.{u}} (a : Y ⟶ constSpace X)

variable [HasSheafify (zariskiTopology Y) AddCommGrpCat.{u}]
variable [HasSheafify (zariskiTopology (constSpace X)) AddCommGrpCat.{u}]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasGlobalSectionsFunctor (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasGlobalSectionsFunctor (zariskiTopology Y) AddCommGrpCat.{u}]

/-- Inverse image along `zariskiMap a` sends a constant abelian sheaf on the constant
simplicial space to the corresponding constant sheaf on `Y_Zar`. -/
def constantSheafCompZariskiPullbackHom :
    constantSheaf (zariskiTopology (constSpace X)) AddCommGrpCat.{u} ⋙
      (zariskiMap a).sheafPullback AddCommGrpCat.{u}
        (zariskiTopology (constSpace X)) (zariskiTopology Y) ⟶
    constantSheaf (zariskiTopology Y) AddCommGrpCat.{u} where
  app M :=
    (((zariskiMap a).sheafAdjunctionContinuous AddCommGrpCat.{u}
          (zariskiTopology (constSpace X)) (zariskiTopology Y)).homEquiv
        ((constantSheaf (zariskiTopology (constSpace X)) AddCommGrpCat.{u}).obj M)
        ((constantSheaf (zariskiTopology Y) AddCommGrpCat.{u}).obj M)).symm
      (((sheafificationAdjunction (zariskiTopology (constSpace X)) AddCommGrpCat.{u}).homEquiv
          ((Functor.const (zariskiSite (constSpace X))ᵒᵖ).obj M)
          (((zariskiMap a).sheafPushforwardContinuous AddCommGrpCat.{u}
              (zariskiTopology (constSpace X)) (zariskiTopology Y)).obj
            ((constantSheaf (zariskiTopology Y) AddCommGrpCat.{u}).obj M))).symm
        ((constCompWhiskeringLeftIso (zariskiSite (constSpace X))ᵒᵖ (zariskiMap a).op).inv.app M ≫
          whiskerLeft (zariskiMap a).op
            ((sheafificationAdjunction (zariskiTopology Y) AddCommGrpCat.{u}).unit.app
              ((Functor.const (zariskiSite Y)ᵒᵖ).obj M))))
  naturality := sorry

/-- Inverse image of constant abelian sheaves along `zariskiMap a` is an isomorphism. -/
instance constantSheafCompZariskiPullbackHom_isIso :
    IsIso (constantSheafCompZariskiPullbackHom a) :=
  sorry

/-- Inverse image along `zariskiMap a` preserves constant abelian sheaves. -/
def constantSheafCompZariskiPullbackIso :
    constantSheaf (zariskiTopology (constSpace X)) AddCommGrpCat.{u} ⋙
      (zariskiMap a).sheafPullback AddCommGrpCat.{u}
        (zariskiTopology (constSpace X)) (zariskiTopology Y) ≅
    constantSheaf (zariskiTopology Y) AddCommGrpCat.{u} :=
  asIso (constantSheafCompZariskiPullbackHom a)

/-- Inverse image along a Zariski augmentation preserves constant abelian sheaves. -/
def constantSheafCompInverseImageIso :
    constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      inverseImage a AddCommGrpCat.{u} ≅
    constantSheaf (zariskiTopology Y) AddCommGrpCat.{u} :=
  (associator
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      ((constProjection X).sheafPushforwardContinuous AddCommGrpCat.{u}
        (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X))
      ((zariskiMap a).sheafPullback AddCommGrpCat.{u}
        (zariskiTopology (constSpace X)) (zariskiTopology Y))).symm ≪≫
    isoWhiskerRight
      ((constProjection X).constantSheafRestrictionIso
        (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X)
        AddCommGrpCat.{u})
      ((zariskiMap a).sheafPullback AddCommGrpCat.{u}
        (zariskiTopology (constSpace X)) (zariskiTopology Y)) ≪≫
    constantSheafCompZariskiPullbackIso a

/-- Underived identification `a_* ⋙ Γ(X, -) ≅ Γ(Y_Zar, -)`. -/
def directImageCompΓIso :
    augmentationPushforward a ⋙
      Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u} ≅
    Sheaf.Γ (zariskiTopology Y) AddCommGrpCat.{u} :=
  (((constantSheafΓAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}).comp
        (inverseImageAdjunction a AddCommGrpCat.{u})).ofNatIsoLeft
      (constantSheafCompInverseImageIso a)).rightAdjointUniq
    (constantSheafΓAdj (zariskiTopology Y) AddCommGrpCat.{u})

/-- `directImageCompΓIso` is the right-adjoint uniqueness isomorphism of
`constantSheafΓAdj` after transporting `a⁻¹ ⊣ a_*` across constant sheaves. -/
theorem directImageCompΓIso_eq :
    directImageCompΓIso a =
      (((constantSheafΓAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}).comp
            (inverseImageAdjunction a AddCommGrpCat.{u})).ofNatIsoLeft
          (constantSheafCompInverseImageIso a)).rightAdjointUniq
        (constantSheafΓAdj (zariskiTopology Y) AddCommGrpCat.{u}) :=
  rfl

variable [(augmentationPushforward a).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (zariskiTopology Y) AddCommGrpCat.{u}))]
variable [(Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))]
variable [(Sheaf.Γ (zariskiTopology Y) AddCommGrpCat.{u}).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (zariskiTopology Y) AddCommGrpCat.{u}))]

/-- Iterated bounded-below unit of `Ra_* ⋙ RΓ(X, -)` as a right-derived model of
`a_* ⋙ Γ(X, -)`. -/
def rGammaDirectImageUnit :
    (augmentationPushforward a ⋙
        Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}).toBoundedBelowDerived ⟶
      DerivedCategory.Plus.Qh ⋙ (plusDirectImageDerived a ⋙ plusGlobalSections X) :=
  (toBoundedBelowDerived.compIso (augmentationPushforward a)
      (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u})).hom ≫
    RightDerived.Composition.iteratedUnit
      (RightDerived.Bounded.unit (augmentationPushforward a))
      (RightDerived.Bounded.unit
        (Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}))

/-- The iterated model `Ra_* ⋙ RΓ(X, -)` is a right-derived functor of
`a_* ⋙ Γ(X, -)`. -/
instance rGammaDirectImage_isRightDerived :
    (plusDirectImageDerived a ⋙ plusGlobalSections X).IsRightDerivedFunctor
      (rGammaDirectImageUnit a)
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (zariskiTopology Y) AddCommGrpCat.{u})) :=
  sorry

/-- Leray identification `Ra_* ⋙ RΓ(X, -) ≅ RΓ(Y_Zar, -)` on `D⁺`. -/
def rGammaDirectImageIso :
    plusDirectImageDerived a ⋙ plusGlobalSections X ≅ plusZariskiGlobalSections Y :=
  RightDerived.natIsoOfIso DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (zariskiTopology Y) AddCommGrpCat.{u}))
    (rGammaDirectImageUnit a)
    (RightDerived.Bounded.unit
      (Sheaf.Γ (zariskiTopology Y) AddCommGrpCat.{u}))
    (NatIso.toBoundedBelowDerived (directImageCompΓIso a))

/-- `rGammaDirectImageIso` is `RightDerived.natIsoOfIso` of `directImageCompΓIso`. -/
theorem rGammaDirectImageIso_eq :
    rGammaDirectImageIso a =
      RightDerived.natIsoOfIso DerivedCategory.Plus.Qh
        (HomotopyCategory.Plus.quasiIso
          (Sheaf (zariskiTopology Y) AddCommGrpCat.{u}))
        (rGammaDirectImageUnit a)
        (RightDerived.Bounded.unit
          (Sheaf.Γ (zariskiTopology Y) AddCommGrpCat.{u}))
        (NatIso.toBoundedBelowDerived (directImageCompΓIso a)) :=
  rfl

/-- Canonical comparison `RΓ(X, -) ⟶ a⁻¹ ⋙ RΓ(Y_Zar, -)` on `D⁺`. -/
def rGammaPullbackComparison :
    plusGlobalSections X ⟶ plusInverseImageDerived a ⋙ plusZariskiGlobalSections Y :=
  whiskerRight (plusDerivedUnit a) (plusGlobalSections X) ≫
    (associator (plusInverseImageDerived a) (plusDirectImageDerived a)
        (plusGlobalSections X)).hom ≫
    whiskerLeft (plusInverseImageDerived a) (rGammaDirectImageIso a).hom

/-- `rGammaPullbackComparison` is the derived unit of `a⁻¹ ⊣ Ra_*`, reassociated and
postcomposed with the Leray identification `rGammaDirectImageIso`. -/
theorem rGammaPullbackComparison_eq :
    rGammaPullbackComparison a =
      whiskerRight (plusDerivedUnit a) (plusGlobalSections X) ≫
        (associator (plusInverseImageDerived a) (plusDirectImageDerived a)
            (plusGlobalSections X)).hom ≫
        whiskerLeft (plusInverseImageDerived a) (rGammaDirectImageIso a).hom :=
  rfl

/-- The component of `rGammaPullbackComparison` at `K` is
`RΓ(X, K) ⟶ RΓ(Y_Zar, a⁻¹ K)`. -/
theorem rGammaPullbackComparison_app
    (K : DerivedCategory.Plus
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})) :
    (rGammaPullbackComparison a).app K =
      (plusGlobalSections X).map ((plusDerivedUnit a).app K) ≫
        (rGammaDirectImageIso a).hom.app ((plusInverseImageDerived a).obj K) :=
  sorry

end CategoryTheory.SimplicialObject

end
