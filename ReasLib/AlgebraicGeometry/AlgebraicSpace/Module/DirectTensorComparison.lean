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

/-! # Tensor comparisons for algebraic-space modules

The commutative and underlying-ring structure sheaves give naturally isomorphic direct images.
These presentations determine a direct-image tensor comparison and its pullback adjunction
transpose. -/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open RingedSite.ToposHom
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.DirectTensorComparison

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The symmetry on modules induced by the commutative module equivalence. -/
@[implicit_reducible]
def symmetric (Z : AlgebraicSpace S) : SymmetricCategory Z.Modules :=
  inferInstanceAs (SymmetricCategory (CategoryTheory.Monoidal.Transported (commModulesEquivalence Z)))

/-- The ringed-topos morphism on the commutative structure-ring presentations. -/
abbrev legacy := toRingedToposHom f (A := commStructureSheaf Y)
  (B := commStructureSheaf X) (structureSheafMap f)

/-- Direct image transported through the commutative module presentations. -/
def transported : X.Modules ⥤ Y.Modules :=
  toCommModules X ⋙ (legacy f).modulePushforward ⋙ ofCommModules Y

/-- The underlying direct-image comparison from the commutative presentation. -/
def forwardUnderlying (M : X.Modules) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Y)).obj ((transported f).obj M) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Y)).obj ((pushforward f).obj M) :=
  (ModulePushforward.forgetIso (legacy f)).hom.app ((toCommModules X).obj M) ≫
    (ModulePushforward.forgetIso (ringedToposHom f)).inv.app M

/-- The underlying direct-image comparison to the commutative presentation. -/
def backwardUnderlying (M : X.Modules) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Y)).obj ((pushforward f).obj M) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Y)).obj ((transported f).obj M) :=
  (ModulePushforward.forgetIso (ringedToposHom f)).hom.app M ≫
    (ModulePushforward.forgetIso (legacy f)).inv.app ((toCommModules X).obj M)

/-- The forward comparison preserves addition and multiplication by scalars. -/
theorem forward_laws (M : X.Modules) :
    (∀ U (x y : ((transported f).obj M).val.obj U),
      Sheaf.InternalModule.underlyingApp (structureSheaf Y) (forwardUnderlying f M) U (x + y) =
        Sheaf.InternalModule.underlyingApp (structureSheaf Y) (forwardUnderlying f M) U x +
          Sheaf.InternalModule.underlyingApp (structureSheaf Y) (forwardUnderlying f M) U y) ∧
    (∀ U (r : (structureSheaf Y).obj.obj U) (x : ((transported f).obj M).val.obj U),
      Sheaf.InternalModule.underlyingApp (structureSheaf Y) (forwardUnderlying f M) U (r • x) =
        r • Sheaf.InternalModule.underlyingApp (structureSheaf Y) (forwardUnderlying f M) U x) := sorry

/-- The backward comparison preserves addition and multiplication by scalars. -/
theorem backward_laws (M : X.Modules) :
    (∀ U (x y : ((pushforward f).obj M).val.obj U),
      Sheaf.InternalModule.underlyingApp (structureSheaf Y) (backwardUnderlying f M) U (x + y) =
        Sheaf.InternalModule.underlyingApp (structureSheaf Y) (backwardUnderlying f M) U x +
          Sheaf.InternalModule.underlyingApp (structureSheaf Y) (backwardUnderlying f M) U y) ∧
    (∀ U (r : (structureSheaf Y).obj.obj U) (x : ((pushforward f).obj M).val.obj U),
      Sheaf.InternalModule.underlyingApp (structureSheaf Y) (backwardUnderlying f M) U (r • x) =
        r • Sheaf.InternalModule.underlyingApp (structureSheaf Y) (backwardUnderlying f M) U x) := sorry

/-- The module direct-image comparison from the commutative presentation. -/
def forward (M : X.Modules) : (transported f).obj M ⟶ (pushforward f).obj M :=
  Sheaf.InternalModule.homOfUnderlying (structureSheaf Y) (forwardUnderlying f M)
    (forward_laws f M).1 (forward_laws f M).2

/-- The module direct-image comparison to the commutative presentation. -/
def backward (M : X.Modules) : (pushforward f).obj M ⟶ (transported f).obj M :=
  Sheaf.InternalModule.homOfUnderlying (structureSheaf Y) (backwardUnderlying f M)
    (backward_laws f M).1 (backward_laws f M).2

/-- The direct-image comparisons are inverse to each other and natural in the module. -/
theorem pushforwardIso_laws :
    (∀ M, forward f M ≫ backward f M = 𝟙 _) ∧
    (∀ M, backward f M ≫ forward f M = 𝟙 _) ∧
    (∀ {M N : X.Modules} (g : M ⟶ N),
      (transported f).map g ≫ forward f N = forward f M ≫ (pushforward f).map g) := sorry

/-- The commutative and underlying-ring presentations give naturally isomorphic direct images. -/
def pushforwardIso : transported f ≅ pushforward f :=
  NatIso.ofComponents (fun M ↦
    { hom := forward f M
      inv := backward f M
      hom_inv_id := (pushforwardIso_laws f).1 M
      inv_hom_id := (pushforwardIso_laws f).2.1 M })
    (fun g ↦ (pushforwardIso_laws f).2.2 g)

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

/-- The canonical tensor comparison for direct image on the actual module categories. -/
def pushforwardTensor (P Q : X.Modules) :
    (pushforward f).obj P ⊗ (pushforward f).obj Q ⟶ (pushforward f).obj (P ⊗ Q) :=
  ((pushforwardIso f).inv.app P ⊗ₘ (pushforwardIso f).inv.app Q) ≫
    transportedTensor f P Q ≫
      (pushforwardIso f).hom.app (P ⊗ Q)

/-- The pullback tensor comparison is the adjunction transpose of the tensor of the units. -/
def pullbackTensor (M N : Y.Modules) :
    (pullback f).obj (M ⊗ N) ⟶ (pullback f).obj M ⊗ (pullback f).obj N :=
  ((pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (((pullbackPushforwardAdjunction f).unit.app M ⊗ₘ
        (pullbackPushforwardAdjunction f).unit.app N) ≫
      pushforwardTensor f ((pullback f).obj M) ((pullback f).obj N))

end AlgebraicGeometry.AlgebraicSpace.Modules.DirectTensorComparison
