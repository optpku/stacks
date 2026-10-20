/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ProjectionFormula
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Braided.Transport
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact

/-! Compare the two specified structure-ring presentations before transporting
their tensor comparisons. The maps are actual underlying direct-image maps;
only their scalar compatibility and naturality laws are deferred. -/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open RingedSite.ToposHom
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.DirectTensorComparison

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Transport the existing symmetry with the same specified module equivalence. -/
@[implicit_reducible]
def symmetric (Z : AlgebraicSpace S) : SymmetricCategory Z.Modules :=
  inferInstanceAs (SymmetricCategory (CategoryTheory.Monoidal.Transported (commModulesEquivalence Z)))

/-- The specified restriction equivalence is additive and strong monoidal. -/
theorem preadditive (Z : AlgebraicSpace S) : MonoidalPreadditive Z.Modules := by
  -- Local instance justification (proof-local temporary data): restriction of scalars preserves addition on the unchanged section maps, supplying a law for the faithful-functor proof.
  letI : (toCommModules Z).Additive := { map_add := by intros; rfl }
  -- Local instance justification (defeq pin): use the inverse strong-monoidal structure of this exact restriction equivalence, matching the public transported tensor data.
  letI : (toCommModules Z).Monoidal :=
    inferInstanceAs ((CategoryTheory.Monoidal.equivalenceTransported
      (commModulesEquivalence Z)).inverse.Monoidal)
  exact monoidalPreadditive_of_faithful (toCommModules Z)

abbrev legacy := toRingedToposHom f (A := commStructureSheaf Y)
  (B := commStructureSheaf X) (structureSheafMap f)

def transported : X.Modules ⥤ Y.Modules :=
  toCommModules X ⋙ (legacy f).modulePushforward ⋙ ofCommModules Y

/-- Both coefficient actions are induced by the same scheme pullback of
functions on each actual étale square. Hence the displayed identity of
underlying direct-image sections is scalar compatible. -/
def forward (M : X.Modules) : (transported f).obj M ⟶ (pushforward f).obj M :=
  Sheaf.InternalModule.homOfUnderlying (structureSheaf Y)
    ((ModulePushforward.forgetIso (legacy f)).hom.app ((toCommModules X).obj M) ≫
      (ModulePushforward.forgetIso (ringedToposHom f)).inv.app M) (by sorry) (by sorry)

def backward (M : X.Modules) : (pushforward f).obj M ⟶ (transported f).obj M :=
  Sheaf.InternalModule.homOfUnderlying (structureSheaf Y)
    ((ModulePushforward.forgetIso (ringedToposHom f)).hom.app M ≫
      (ModulePushforward.forgetIso (legacy f)).inv.app ((toCommModules X).obj M)) (by sorry) (by sorry)

def pushforwardIso : transported f ≅ pushforward f :=
  NatIso.ofComponents (fun M ↦
    { hom := forward f M
      inv := backward f M
      hom_inv_id := by sorry
      inv_hom_id := by sorry }) (by sorry)

/-- The tensor maps of the explicit equivalence insert its actual units;
the two monoidal presentations are not identified by definitional equality. -/
def transportedTensor (P Q : X.Modules) :
    (transported f).obj P ⊗ (transported f).obj Q ⟶ (transported f).obj (P ⊗ Q) :=
  (ofCommModules Y).map
    (((commModulesEquivalence Y).unitIso.inv.app
        ((legacy f).modulePushforward.obj ((toCommModules X).obj P)) ⊗ₘ
      (commModulesEquivalence Y).unitIso.inv.app
        ((legacy f).modulePushforward.obj ((toCommModules X).obj Q))) ≫
      modulePushforward_tensorComparison f (A := commStructureSheaf Y)
        (B := commStructureSheaf X) (structureSheafMap f)
        ((toCommModules X).obj P) ((toCommModules X).obj Q) ≫
      (legacy f).modulePushforward.map
        ((commModulesEquivalence X).unitIso.hom.app
          (((toCommModules X).obj P) ⊗ ((toCommModules X).obj Q))))

def pushforwardTensor (P Q : X.Modules) :
    (pushforward f).obj P ⊗ (pushforward f).obj Q ⟶ (pushforward f).obj (P ⊗ Q) :=
  ((pushforwardIso f).inv.app P ⊗ₘ (pushforwardIso f).inv.app Q) ≫
    transportedTensor f P Q ≫
      (pushforwardIso f).hom.app (P ⊗ Q)

def pullbackTensor (M N : Y.Modules) :
    (pullback f).obj (M ⊗ N) ⟶ (pullback f).obj M ⊗ (pullback f).obj N :=
  ((pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (((pullbackPushforwardAdjunction f).unit.app M ⊗ₘ
        (pullbackPushforwardAdjunction f).unit.app N) ≫
      pushforwardTensor f ((pullback f).obj M) ((pullback f).obj N))

end AlgebraicGeometry.AlgebraicSpace.Modules.DirectTensorComparison
