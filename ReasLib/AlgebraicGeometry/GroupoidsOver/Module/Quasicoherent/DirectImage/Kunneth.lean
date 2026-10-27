/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.StructureSheaf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.DirectImage.Adjunction
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.DirectImage.Tensor
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.PullbackCoherence
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale.SmallSections
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange

/-! # Quasi-coherent Kunneth comparison -/

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Adjunction
open AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver
open CategoryTheory.MonoidalCategory CategoryTheory.ObjectProperty
open FiberedCategoryOver.Groupoids
open SheafOfModules.RingedSite
open scoped Bicategory
noncomputable section
universe u
namespace AlgebraicGeometry.GroupoidsOver.QCoh
variable {S : Scheme.{u}}

/-- The obvious morphism `f : Y ×_X Z ⟶ X` from the chosen 2-fibre product,
as `TwoFibreProduct.fst a b ≫ a`. -/
abbrev fibreProductHom {X Y Z : GroupoidsOver S} (a : Y ⟶ X) (b : Z ⟶ X) :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b ⟶ X :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u} a b ≫ a

/-- `fibreProductHom a b` is the composite of the first 2-fibre-product
projection with `a`. -/
theorem fibreProductHom_eq {X Y Z : GroupoidsOver S} (a : Y ⟶ X) (b : Z ⟶ X) :
    fibreProductHom a b = TwoFibreProduct.fst.{u + 1, u, u + 1, u} a b ≫ a :=
  rfl

/-- The canonical 2-isomorphism identifying the two composites from the chosen
2-fibre product to `X`. -/
def fibreProductHom_comparison {X Y Z : GroupoidsOver S} (a : Y ⟶ X) (b : Z ⟶ X) :
    fibreProductHom a b ≅
      TwoFibreProduct.snd.{u + 1, u, u + 1, u} a b ≫ b :=
  TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} a b

/-- `fibreProductHom_comparison a b` is the chosen 2-fibre-product comparison
cell. -/
theorem fibreProductHom_comparison_eq {X Y Z : GroupoidsOver S}
    (a : Y ⟶ X) (b : Z ⟶ X) :
    fibreProductHom_comparison a b =
      TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} a b :=
  rfl

/-- The 2-cell `𝟭 ⋙ pullback f ≅ pullback a ⋙ pullback fst` of the triangle
`fst ≫ a = f`. -/
def kunnethPullbackSquare {X Y Z : GroupoidsOver S}
    (a : Y ⟶ X) (b : Z ⟶ X) :
    𝟭 (QCoh X) ⋙ pullback (fibreProductHom a b) ≅
      pullback a ⋙
        pullback (TwoFibreProduct.fst.{u + 1, u, u + 1, u} a b) :=
  (pullback (fibreProductHom a b)).leftUnitor ≪≫
    pullback_comp (TwoFibreProduct.fst.{u + 1, u, u + 1, u} a b) a

/-- The 2-cell `𝟭 ⋙ pullback f ≅ pullback b ⋙ pullback snd` obtained by
transporting along the 2-fibre-product comparison isomorphism. -/
def kunnethPullbackSquare_right {X Y Z : GroupoidsOver S}
    (a : Y ⟶ X) (b : Z ⟶ X) :
    𝟭 (QCoh X) ⋙ pullback (fibreProductHom a b) ≅
      pullback b ⋙
        pullback (TwoFibreProduct.snd.{u + 1, u, u + 1, u} a b) :=
  (pullback (fibreProductHom a b)).leftUnitor ≪≫
    (pullbackIso (fibreProductHom_comparison a b)).symm ≪≫
      pullback_comp (TwoFibreProduct.snd.{u + 1, u, u + 1, u} a b) b

variable {X Y Z : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
variable (a : Y ⟶ X) (b : Z ⟶ X)
variable [AlgebraicStack.QuasiCompact a] [AlgebraicStack.QuasiSeparated a]
variable [AlgebraicStack.QuasiCompact b] [AlgebraicStack.QuasiSeparated b]
variable [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b)]
variable [AlgebraicStack.QuasiCompact (fibreProductHom a b)]
variable [AlgebraicStack.QuasiSeparated (fibreProductHom a b)]

/-- Relative pullback map `a_{QCoh,*} O_Y ⟶ f_{QCoh,*} fst^* O_Y` induced by the
triangle `fst ≫ a = f`. -/
def relativePullbackMap :
    (directImage a).obj (structureSheaf Y) ⟶
      (directImage (fibreProductHom a b)).obj
        ((pullback (TwoFibreProduct.fst.{u + 1, u, u + 1, u} a b)).obj
          (structureSheaf Y)) :=
  DerivedBaseChange.app
    (pullbackDirectImageAdjunction a)
    (pullbackDirectImageAdjunction (fibreProductHom a b))
    (kunnethPullbackSquare a b) (structureSheaf Y)

/-- Relative pullback map `b_{QCoh,*} O_Z ⟶ f_{QCoh,*} snd^* O_Z` induced by the
triangle `snd ≫ b ≅ f`. -/
def relativePullbackMap_right :
    (directImage b).obj (structureSheaf Z) ⟶
      (directImage (fibreProductHom a b)).obj
        ((pullback (TwoFibreProduct.snd.{u + 1, u, u + 1, u} a b)).obj
          (structureSheaf Z)) :=
  DerivedBaseChange.app
    (pullbackDirectImageAdjunction b)
    (pullbackDirectImageAdjunction (fibreProductHom a b))
    (kunnethPullbackSquare_right a b) (structureSheaf Z)

/-- Relative structure-sheaf pushforward
`a_{QCoh,*} O_Y ⟶ f_{QCoh,*} O_{Y ×_X Z}` obtained from the relative pullback
map and `structureSheafPullbackInv`. -/
def relativeStructurePushforward :
    (directImage a).obj (structureSheaf Y) ⟶
      (directImage (fibreProductHom a b)).obj
        (structureSheaf (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b)) :=
  relativePullbackMap a b ≫
    (directImage (fibreProductHom a b)).map
      (structureSheafPullbackInv
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} a b))

/-- Relative structure-sheaf pushforward
`b_{QCoh,*} O_Z ⟶ f_{QCoh,*} O_{Y ×_X Z}` obtained from the right relative
pullback map and `structureSheafPullbackInv`. -/
def relativeStructurePushforward_right :
    (directImage b).obj (structureSheaf Z) ⟶
      (directImage (fibreProductHom a b)).obj
        (structureSheaf (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b)) :=
  relativePullbackMap_right a b ≫
    (directImage (fibreProductHom a b)).map
      (structureSheafPullbackInv
        (TwoFibreProduct.snd.{u + 1, u, u + 1, u} a b))

/-- The canonical underived Künneth morphism
`a_{QCoh,*} O_Y ⊗_{O_X} b_{QCoh,*} O_Z ⟶ f_{QCoh,*} O_{Y ×_X Z}` of
quasi-coherent structure sheaves. -/
def kunnethMap :
    Fppf.tensor ((directImage a).obj (structureSheaf Y))
      ((directImage b).obj (structureSheaf Z)) ⟶
      (directImage (fibreProductHom a b)).obj
        (structureSheaf (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b)) :=
  tensorHom (relativeStructurePushforward a b)
      (relativeStructurePushforward_right a b) ≫
    directImage_tensorComparison (fibreProductHom a b)
        (toLQCohFbcAdjunction X)
        (structureSheaf (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b))
        (structureSheaf (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b)) ≫
      (directImage (fibreProductHom a b)).map
        (structureSheafMul (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b))

/-- `kunnethMap a b` is the tensor of the two relative structure-sheaf
pushforwards, followed by `directImage_tensorComparison` and multiplication of
`O_{Y ×_X Z}`. -/
theorem kunnethMap_spec :
    kunnethMap a b =
      tensorHom (relativeStructurePushforward a b)
          (relativeStructurePushforward_right a b) ≫
        directImage_tensorComparison (fibreProductHom a b)
            (toLQCohFbcAdjunction X)
            (structureSheaf (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b))
            (structureSheaf (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b)) ≫
          (directImage (fibreProductHom a b)).map
            (structureSheafMul
              (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b)) :=
  rfl

/-- Under representability, flatness, and finiteness hypotheses, the Künneth
comparison of structure sheaves is an isomorphism. -/
@[stacks 0GRN]
theorem kunnethMap_isIso {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (a : Y ⟶ X) (b : Z ⟶ X)
    (ha : FiberedCategoryOver.Groupoids.relativelyRepresentable a)
    (hb : FiberedCategoryOver.Groupoids.relativelyRepresentable b)
    [AlgebraicStack.QuasiCompact a] [AlgebraicStack.QuasiSeparated a]
    [AlgebraicStack.Flat a]
    [AlgebraicStack.QuasiCompact b] [AlgebraicStack.QuasiSeparated b]
    [AlgebraicStack.Flat b]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b)]
    [AlgebraicStack.QuasiCompact (fibreProductHom a b)]
    [AlgebraicStack.QuasiSeparated (fibreProductHom a b)] :
    IsIso (kunnethMap a b) := sorry

/-- The Künneth comparison is invertible when representability is supplied by facts. -/
instance kunnethMap_isIso_instance {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (a : Y ⟶ X) (b : Z ⟶ X)
    [ha : Fact (FiberedCategoryOver.Groupoids.relativelyRepresentable a)]
    [hb : Fact (FiberedCategoryOver.Groupoids.relativelyRepresentable b)]
    [AlgebraicStack.QuasiCompact a] [AlgebraicStack.QuasiSeparated a]
    [AlgebraicStack.Flat a] [AlgebraicStack.QuasiCompact b]
    [AlgebraicStack.QuasiSeparated b] [AlgebraicStack.Flat b]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} a b)]
    [AlgebraicStack.QuasiCompact (fibreProductHom a b)]
    [AlgebraicStack.QuasiSeparated (fibreProductHom a b)] :
    IsIso (kunnethMap a b) := kunnethMap_isIso a b ha.out hb.out
end AlgebraicGeometry.GroupoidsOver.QCoh
