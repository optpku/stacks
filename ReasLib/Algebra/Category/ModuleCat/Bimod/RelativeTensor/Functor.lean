/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Bimod.Linear
public import ReasLib.Algebra.Category.ModuleCat.Bimod.RelativeTensor
public import ReasLib.Algebra.Category.ModuleCat.Bimod.TensorHom
public import ReasLib.CategoryTheory.Monoidal.Bimod.Tensor.Linear
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ordinary relative tensor functors in `ModuleCat`

For a fixed ordinary `(A, B)`-bimodule `N`, this file compares two functors on ordinary
right `A`-modules.  The first realizes a module categorically and then applies Mathlib's
balanced tensor functor.  The second forms the explicit relative tensor quotient and realizes
its quotient-native right `B`-module structure.  Keeping the latter construction direct avoids
introducing a second ground-ring action by an additional restriction-of-scalars functor.
-/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra RelativeTensor TensorProduct

noncomputable section

universe u

namespace Module.Bimodule.RelativeTensor

variable {R A B N : Type u}
variable [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [AddCommGroup N] [Module R N] [Module A N] [Module Bᵐᵒᵖ N]
variable [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N]
variable [SMulCommClass A Bᵐᵒᵖ N]

/-- Realize ordinary right `A`-modules and tensor them categorically with the fixed
`(A, B)`-bimodule `N`. -/
@[stacks 09LN "categorical relative tensor functor"]
noncomputable abbrev categoricalFunctor (N : Type u) [AddCommGroup N] [Module R N]
    [Module A N] [Module Bᵐᵒᵖ N] [IsScalarTower R A N]
    [IsScalarTower R Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N] :
    ModuleCat.{u} Aᵐᵒᵖ ⥤
      CategoryTheory.Bimod.RightModule (algebraMon (R := R) B) :=
  rightModuleFunctor (R := R) (A := A) ⋙
    CategoryTheory.Bimod.tensorRight (toBimod (R := R) (A := A) (B := B) N)

/-- Categorical relative tensoring with a fixed ordinary bimodule is additive. -/
@[stacks 09LN "additive categorical relative tensor functor"]
theorem categoricalFunctorAdditive :
    (categoricalFunctor (R := R) (A := A) (B := B) N).Additive := sorry

/-- Categorical relative tensoring with a fixed ordinary bimodule is `R`-linear. -/
@[stacks 09LN "linear categorical relative tensor functor"]
theorem categoricalFunctorLinear :
    Functor.Linear R
      (categoricalFunctor (R := R) (A := A) (B := B) N) := sorry

/-- On objects, `categoricalFunctor N` is Mathlib's coequalizer-based balanced tensor
product. -/
@[simp, stacks 09LN "categorical relative tensor functor on objects"]
theorem categoricalFunctor_obj (M : ModuleCat.{u} Aᵐᵒᵖ) :
    (categoricalFunctor (R := R) (A := A) (B := B) N).obj M =
      (toRightModule (R := R) (A := A)
          (RightModuleFunctor.restricted (R := R) M)).tensorBimod
        (toBimod (R := R) (A := A) (B := B) N) := sorry

/-- On morphisms, `categoricalFunctor N` is right whiskering by the fixed categorical
bimodule. -/
@[simp, stacks 09LN "categorical relative tensor functor on morphisms"]
theorem categoricalFunctor_map {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M') :
    (categoricalFunctor (R := R) (A := A) (B := B) N).map f =
      Bimod.whiskerRight (RightModuleFunctor.map (R := R) f)
        (toBimod (R := R) (A := A) (B := B) N) := sorry

/-- The categorical fixed-`N` tensor functor maps pure tensors in the first factor as
expected. -/
@[simp, stacks 09LN "categorical relative tensor functor maps pure tensors"]
theorem categoricalFunctor_map_tmul {M M' : ModuleCat.{u} Aᵐᵒᵖ}
    (f : M ⟶ M') (m : M) (n : N) :
    ((categoricalFunctor (R := R) (A := A) (B := B) N).map f).hom
        (tensorBimodMk (R := R) (A := A) (B := B)
          (M := RightModuleFunctor.restricted (R := R) M) (N := N) (m ⊗ₜ[R] n)) =
      tensorBimodMk (R := R) (A := A) (B := B)
        (M := RightModuleFunctor.restricted (R := R) M') (N := N)
        (f.hom m ⊗ₜ[R] n) := sorry

namespace RealizationFunctor

/-- The explicit relative tensor quotient attached to an ordinary right `A`-module and the
fixed bimodule `N`. -/
@[stacks 09LN "explicit fixed-bimodule relative tensor carrier"]
abbrev product (N : Type u) [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] (M : ModuleCat.{u} Aᵐᵒᵖ) :=
  Product (R := R) (A := A)
    (M := RightModuleFunctor.restricted (R := R) M) (N := N)

/-- The quotient-native categorical right `B`-module attached to an ordinary right
`A`-module. -/
@[stacks 09LN "explicit relative tensor as a categorical right module"]
noncomputable def obj (N : Type u) [AddCommGroup N] [Module R N] [Module A N]
    [Module Bᵐᵒᵖ N] [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N]
    [SMulCommClass A Bᵐᵒᵖ N] (M : ModuleCat.{u} Aᵐᵒᵖ) :
    CategoryTheory.Bimod.RightModule (algebraMon (R := R) B) :=
  toRightModule (R := R) (A := B) (product (R := R) (A := A) N M)

/-- The map on explicit relative tensor quotients induced by an ordinary right-linear map. -/
@[stacks 09LN "explicit relative tensor linear map in the first factor"]
def linearMap {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M') :
    product (R := R) (A := A) N M →ₗ[Bᵐᵒᵖ]
      product (R := R) (A := A) N M' :=
  mapLeft (R := R) (A := A) (B := B)
    (M := RightModuleFunctor.restricted (R := R) M)
    (M' := RightModuleFunctor.restricted (R := R) M') (N := N) f.hom

/-- The categorical right `B`-module morphism induced on explicit relative tensor
quotients. -/
@[stacks 09LN "explicit relative tensor functor on morphisms"]
def map {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M') :
    obj (R := R) (A := A) (B := B) N M ⟶
      obj (R := R) (A := A) (B := B) N M' :=
  ToRightModule.map (R := R) (N := product (R := R) (A := A) N M)
    (N' := product (R := R) (A := A) N M') (linearMap (R := R) (B := B) f)

/-- The explicit linear map on relative tensor quotients evaluates on pure tensors in the first
factor. -/
@[simp, stacks 09LN "explicit relative tensor linear map on pure tensors"]
theorem linearMap_tmul {M M' : ModuleCat.{u} Aᵐᵒᵖ}
    (f : M ⟶ M') (m : M) (n : N) :
    linearMap (R := R) (A := A) (B := B) (N := N) f
        (tmul (R := R) (A := A)
          (M := RightModuleFunctor.restricted (R := R) M) m n) =
      tmul (R := R) (A := A)
        (M := RightModuleFunctor.restricted (R := R) M') (f.hom m) n := sorry

/-- The underlying ground-ring map of an explicit relative tensor morphism is restriction of its
right-linear map. -/
@[simp, stacks 09LN "underlying map of the explicit relative tensor morphism"]
theorem map_hom {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M') :
    (map (R := R) (A := A) (B := B) (N := N) f).hom =
      ModuleCat.ofHom ((linearMap (R := R) (A := A) (B := B) (N := N) f).restrictScalars R) :=
  sorry

/-- Explicit relative tensor morphisms evaluate by their underlying right-linear maps. -/
@[simp, stacks 09LN "explicit relative tensor morphism evaluation"]
theorem map_apply {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M')
    (x : product (R := R) (A := A) N M) :
    (map (R := R) (A := A) (B := B) (N := N) f).hom x =
      linearMap (R := R) (A := A) (B := B) (N := N) f x := sorry

/-- The identity ordinary module morphism induces the identity explicit relative tensor
morphism. -/
@[simp, stacks 09LN "identity explicit relative tensor morphism"]
theorem map_id (M : ModuleCat.{u} Aᵐᵒᵖ) :
    map (R := R) (A := A) (B := B) (N := N) (𝟙 M) =
      𝟙 (obj (R := R) (A := A) (B := B) N M) := sorry

/-- Explicit relative tensor morphisms preserve composition. -/
@[simp, stacks 09LN "composition of explicit relative tensor morphisms"]
theorem map_comp {M M' M'' : ModuleCat.{u} Aᵐᵒᵖ}
    (f : M ⟶ M') (g : M' ⟶ M'') :
    map (R := R) (A := A) (B := B) (N := N) (f ≫ g) =
      map (R := R) (A := A) (B := B) (N := N) f ≫
        map (R := R) (A := A) (B := B) (N := N) g := sorry

end RealizationFunctor

/-- Form the explicit relative tensor quotient with `N`, retaining its quotient-native
ground-ring and right `B` actions. -/
@[stacks 09LN "explicit relative tensor realization functor"]
noncomputable def realizationFunctor (N : Type u) [AddCommGroup N] [Module R N]
    [Module A N] [Module Bᵐᵒᵖ N] [IsScalarTower R A N]
    [IsScalarTower R Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N] :
    ModuleCat.{u} Aᵐᵒᵖ ⥤
      CategoryTheory.Bimod.RightModule (algebraMon (R := R) B) where
  obj M := RealizationFunctor.obj (R := R) (A := A) (B := B) N M
  map f := RealizationFunctor.map (R := R) (A := A) (B := B) (N := N) f
  map_id := sorry
  map_comp := sorry

/-- The explicit categorical realization of relative tensoring is additive. -/
@[stacks 09LN "additive explicit relative tensor realization"]
instance realizationFunctorAdditive :
    (realizationFunctor (R := R) (A := A) (B := B) N).Additive := sorry

/-- The explicit categorical realization of relative tensoring is `R`-linear. -/
@[stacks 09LN "linear explicit relative tensor realization"]
instance realizationFunctorLinear :
    Functor.Linear R
      (realizationFunctor (R := R) (A := A) (B := B) N) := sorry

/-- On objects, `realizationFunctor N` is the categorical right module carried by the explicit
relative tensor quotient. -/
@[simp, stacks 09LN "explicit relative tensor realization functor on objects"]
theorem realizationFunctor_obj (M : ModuleCat.{u} Aᵐᵒᵖ) :
    (realizationFunctor (R := R) (A := A) (B := B) N).obj M =
      toRightModule (R := R) (A := B)
        (RealizationFunctor.product (R := R) (A := A) N M) := sorry

/-- On morphisms, `realizationFunctor N` is induced by `mapLeft` on the explicit quotient. -/
@[simp, stacks 09LN "explicit relative tensor realization functor on morphisms"]
theorem realizationFunctor_map {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M') :
    (realizationFunctor (R := R) (A := A) (B := B) N).map f =
      RealizationFunctor.map (R := R) (A := A) (B := B) (N := N) f := sorry

/-- The explicit relative tensor functor maps a pure tensor in the first factor as expected. -/
@[simp, stacks 09LN "explicit relative tensor realization functor maps pure tensors"]
theorem realizationFunctor_map_tmul {M M' : ModuleCat.{u} Aᵐᵒᵖ}
    (f : M ⟶ M') (m : M) (n : N) :
    ((realizationFunctor (R := R) (A := A) (B := B) N).map f).hom
        (tmul (R := R) (A := A)
          (M := RightModuleFunctor.restricted (R := R) M) m n) =
      tmul (R := R) (A := A)
        (M := RightModuleFunctor.restricted (R := R) M') (f.hom m) n := sorry

/-- The objectwise concrete-categorical relative tensor comparison intertwines the
categorical and explicit fixed-`N` tensor maps. -/
@[reassoc, stacks 09LN "naturality of the ordinary relative tensor comparison"]
theorem realizationIso_naturality {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M') :
    (categoricalFunctor (R := R) (A := A) (B := B) N).map f ≫
        (tensorBimodIso (R := R) (A := A) (B := B)
          (M := RightModuleFunctor.restricted (R := R) M') (N := N)).hom =
      (tensorBimodIso (R := R) (A := A) (B := B)
          (M := RightModuleFunctor.restricted (R := R) M) (N := N)).hom ≫
        (realizationFunctor (R := R) (A := A) (B := B) N).map f := sorry

/-- The categorical and explicit fixed-`N` relative tensor functors are naturally
isomorphic. -/
@[stacks 09LN "ordinary relative tensor functor comparison"]
noncomputable def realizationIso (N : Type u) [AddCommGroup N] [Module R N]
    [Module A N] [Module Bᵐᵒᵖ N] [IsScalarTower R A N]
    [IsScalarTower R Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N] :
    categoricalFunctor (R := R) (A := A) (B := B) N ≅
      realizationFunctor (R := R) (A := A) (B := B) N :=
  NatIso.ofComponents
    (fun M ↦ tensorBimodIso (R := R) (A := A) (B := B)
      (M := RightModuleFunctor.restricted (R := R) M) (N := N))
    (fun f ↦ realizationIso_naturality (R := R) (A := A) (B := B) (N := N) f)

/-- The inverse ordinary relative tensor comparison is natural in the right-module input. -/
@[reassoc, stacks 09LN "inverse naturality of the ordinary relative tensor comparison"]
theorem realizationIso_inv_naturality {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M') :
    (realizationFunctor (R := R) (A := A) (B := B) N).map f ≫
        (realizationIso (R := R) (A := A) (B := B) N).inv.app M' =
      (realizationIso (R := R) (A := A) (B := B) N).inv.app M ≫
        (categoricalFunctor (R := R) (A := A) (B := B) N).map f := sorry

/-- The component of the ordinary relative tensor comparison is the pointwise
concrete-categorical comparison. -/
@[simp, stacks 09LN "component of the ordinary relative tensor functor comparison"]
theorem realizationIso_app (M : ModuleCat.{u} Aᵐᵒᵖ) :
    (realizationIso (R := R) (A := A) (B := B) N).app M =
      tensorBimodIso (R := R) (A := A) (B := B)
        (M := RightModuleFunctor.restricted (R := R) M) (N := N) := sorry

/-- The forward component of `realizationIso N` is the canonical map from the categorical
balanced tensor product to the explicit quotient. -/
@[simp, stacks 09LN "forward component of the ordinary relative tensor comparison"]
theorem realizationIso_hom_app (M : ModuleCat.{u} Aᵐᵒᵖ) :
    (realizationIso (R := R) (A := A) (B := B) N).hom.app M =
      (tensorBimodIso (R := R) (A := A) (B := B)
        (M := RightModuleFunctor.restricted (R := R) M) (N := N)).hom := sorry

/-- The inverse component of `realizationIso N` is the canonical map from the explicit
quotient to the categorical balanced tensor product. -/
@[simp, stacks 09LN "inverse component of the ordinary relative tensor comparison"]
theorem realizationIso_inv_app (M : ModuleCat.{u} Aᵐᵒᵖ) :
    (realizationIso (R := R) (A := A) (B := B) N).inv.app M =
      (tensorBimodIso (R := R) (A := A) (B := B)
        (M := RightModuleFunctor.restricted (R := R) M) (N := N)).inv := sorry

/-- The forward comparison component sends a categorical pure tensor to its explicit relative
tensor class. -/
@[simp, stacks 09LN "forward ordinary relative tensor comparison on pure tensors"]
theorem realizationIso_hom_app_tmul (M : ModuleCat.{u} Aᵐᵒᵖ) (m : M) (n : N) :
    ((realizationIso (R := R) (A := A) (B := B) N).hom.app M).hom
        (tensorBimodMk (R := R) (A := A) (B := B)
          (M := RightModuleFunctor.restricted (R := R) M) (N := N) (m ⊗ₜ[R] n)) =
      tmul (R := R) (A := A)
        (M := RightModuleFunctor.restricted (R := R) M) m n := sorry

/-- The inverse comparison component sends an explicit pure relative tensor to its categorical
coequalizer class. -/
@[simp, stacks 09LN "inverse ordinary relative tensor comparison on pure tensors"]
theorem realizationIso_inv_app_tmul (M : ModuleCat.{u} Aᵐᵒᵖ) (m : M) (n : N) :
    ((realizationIso (R := R) (A := A) (B := B) N).inv.app M).hom
        (tmul (R := R) (A := A)
          (M := RightModuleFunctor.restricted (R := R) M) m n) =
      tensorBimodMk (R := R) (A := A) (B := B)
        (M := RightModuleFunctor.restricted (R := R) M) (N := N) (m ⊗ₜ[R] n) := sorry

namespace Ordinary

/-- The universe-polymorphic ordinary relative tensor functor, followed by realization as a
categorical right module. -/
@[stacks 09LN "ordinary relative tensor functor as categorical right modules"]
noncomputable abbrev functor (N : Type u) [AddCommGroup N] [Module R N]
    [Module A N] [Module Bᵐᵒᵖ N] [IsScalarTower R A N]
    [IsScalarTower R Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N] :
    ModuleCat.{u} Aᵐᵒᵖ ⥤
      CategoryTheory.Bimod.RightModule (algebraMon (R := R) B) :=
  Module.Bimodule.RelativeTensor.functor (R := R) (A := A) (B := B) N ⋙
    rightModuleFunctor (R := R) (A := B)

/-- At each ordinary right module, scalar-restriction comparison identifies the realized
ordinary tensor object with its quotient-native categorical realization. -/
@[stacks 09LN "objectwise ordinary relative tensor realization comparison"]
noncomputable def appIso (N : Type u) [AddCommGroup N] [Module R N]
    [Module A N] [Module Bᵐᵒᵖ N] [IsScalarTower R A N]
    [IsScalarTower R Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
    (M : ModuleCat.{u} Aᵐᵒᵖ) :
    (functor (R := R) (A := A) (B := B) N).obj M ≅
      (Module.Bimodule.RelativeTensor.realizationFunctor
        (R := R) (A := A) (B := B) N).obj M where
  hom :=
    { hom := (ModuleCat.RestrictScalars.identityIso
        (R := R) (S := Bᵐᵒᵖ) (RealizationFunctor.product (R := R) (A := A) N M)).hom
      left_act_hom := sorry
      right_act_hom := sorry }
  inv :=
    { hom := (ModuleCat.RestrictScalars.identityIso
        (R := R) (S := Bᵐᵒᵖ) (RealizationFunctor.product (R := R) (A := A) N M)).inv
      left_act_hom := sorry
      right_act_hom := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward objectwise ordinary realization comparison is the identity on elements. -/
@[simp, stacks 09LN "forward ordinary relative tensor realization comparison on elements"]
theorem appIso_hom_apply (M : ModuleCat.{u} Aᵐᵒᵖ)
    (x : ((functor (R := R) (A := A) (B := B) N).obj M).X) :
    (appIso (R := R) (A := A) (B := B) N M).hom.hom x = x := sorry

/-- The inverse objectwise ordinary realization comparison is the identity on elements. -/
@[simp, stacks 09LN "inverse ordinary relative tensor realization comparison on elements"]
theorem appIso_inv_apply (M : ModuleCat.{u} Aᵐᵒᵖ)
    (x : ((Module.Bimodule.RelativeTensor.realizationFunctor
      (R := R) (A := A) (B := B) N).obj M).X) :
    (appIso (R := R) (A := A) (B := B) N M).inv.hom x = x := sorry

/-- The objectwise ordinary realization comparison is natural in the right-module input. -/
@[reassoc, stacks 09LN "naturality of ordinary relative tensor realization"]
theorem realizationIso_naturality {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M') :
    (functor (R := R) (A := A) (B := B) N).map f ≫
        (appIso (R := R) (A := A) (B := B) N M').hom =
      (appIso (R := R) (A := A) (B := B) N M).hom ≫
        (Module.Bimodule.RelativeTensor.realizationFunctor
          (R := R) (A := A) (B := B) N).map f := sorry

/-- Ordinary relative tensor followed by categorical realization is naturally isomorphic to
the quotient-native realization functor. -/
@[stacks 09LN "ordinary relative tensor realization comparison"]
noncomputable def realizationIso (N : Type u) [AddCommGroup N] [Module R N]
    [Module A N] [Module Bᵐᵒᵖ N] [IsScalarTower R A N]
    [IsScalarTower R Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N] :
    functor (R := R) (A := A) (B := B) N ≅
      Module.Bimodule.RelativeTensor.realizationFunctor
        (R := R) (A := A) (B := B) N :=
  NatIso.ofComponents
    (fun M ↦ appIso (R := R) (A := A) (B := B) N M)
    (fun f ↦ realizationIso_naturality (R := R) (A := A) (B := B) (N := N) f)

/-- The inverse ordinary realization comparison is natural in the right-module input. -/
@[reassoc, stacks 09LN "inverse naturality of ordinary tensor realization"]
theorem realizationIso_inv_naturality {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M') :
    (Module.Bimodule.RelativeTensor.realizationFunctor
        (R := R) (A := A) (B := B) N).map f ≫
        (realizationIso (R := R) (A := A) (B := B) N).inv.app M' =
      (realizationIso (R := R) (A := A) (B := B) N).inv.app M ≫
        (functor (R := R) (A := A) (B := B) N).map f := sorry

/-- The component of the ordinary realization comparison is its objectwise scalar-restriction
comparison. -/
@[simp, stacks 09LN "component of the ordinary relative tensor realization comparison"]
theorem realizationIso_app (M : ModuleCat.{u} Aᵐᵒᵖ) :
    (realizationIso (R := R) (A := A) (B := B) N).app M =
      appIso (R := R) (A := A) (B := B) N M := sorry

/-- The forward component of the ordinary realization comparison is the objectwise forward
comparison. -/
@[simp, stacks 09LN "forward component of the ordinary tensor realization comparison"]
theorem realizationIso_hom_app (M : ModuleCat.{u} Aᵐᵒᵖ) :
    (realizationIso (R := R) (A := A) (B := B) N).hom.app M =
      (appIso (R := R) (A := A) (B := B) N M).hom := sorry

/-- The inverse component of the ordinary realization comparison is the objectwise inverse
comparison. -/
@[simp, stacks 09LN "inverse component of the ordinary tensor realization comparison"]
theorem realizationIso_inv_app (M : ModuleCat.{u} Aᵐᵒᵖ) :
    (realizationIso (R := R) (A := A) (B := B) N).inv.app M =
      (appIso (R := R) (A := A) (B := B) N M).inv := sorry

/-- The categorical balanced tensor functor is naturally isomorphic to ordinary relative tensor
followed by categorical realization. -/
@[stacks 09LN "categorical and ordinary relative tensor functors"]
noncomputable def categoricalIso (N : Type u) [AddCommGroup N] [Module R N]
    [Module A N] [Module Bᵐᵒᵖ N] [IsScalarTower R A N]
    [IsScalarTower R Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N] :
    Module.Bimodule.RelativeTensor.categoricalFunctor
        (R := R) (A := A) (B := B) N ≅
      functor (R := R) (A := A) (B := B) N :=
  (Module.Bimodule.RelativeTensor.realizationIso
    (R := R) (A := A) (B := B) N).trans
      (realizationIso (R := R) (A := A) (B := B) N).symm

/-- The categorical-to-ordinary comparison component is the composite through the explicit
relative tensor realization. -/
@[simp, stacks 09LN "component of the categorical-to-ordinary tensor comparison"]
theorem categoricalIso_app (M : ModuleCat.{u} Aᵐᵒᵖ) :
    (categoricalIso (R := R) (A := A) (B := B) N).app M =
      (Module.Bimodule.RelativeTensor.realizationIso
          (R := R) (A := A) (B := B) N).app M ≪≫
        (realizationIso (R := R) (A := A) (B := B) N).symm.app M := sorry

/-- The forward categorical-to-ordinary component factors through the explicit relative tensor
realization. -/
@[simp, stacks 09LN "forward component of the categorical-to-ordinary tensor comparison"]
theorem categoricalIso_hom_app (M : ModuleCat.{u} Aᵐᵒᵖ) :
    (categoricalIso (R := R) (A := A) (B := B) N).hom.app M =
      (Module.Bimodule.RelativeTensor.realizationIso
          (R := R) (A := A) (B := B) N).hom.app M ≫
        (realizationIso (R := R) (A := A) (B := B) N).inv.app M := sorry

/-- The inverse ordinary-to-categorical component factors through the explicit relative tensor
realization. -/
@[simp, stacks 09LN "inverse component of the categorical-to-ordinary tensor comparison"]
theorem categoricalIso_inv_app (M : ModuleCat.{u} Aᵐᵒᵖ) :
    (categoricalIso (R := R) (A := A) (B := B) N).inv.app M =
      (realizationIso (R := R) (A := A) (B := B) N).hom.app M ≫
        (Module.Bimodule.RelativeTensor.realizationIso
          (R := R) (A := A) (B := B) N).inv.app M := sorry

/-- The categorical, ordinary, and explicit relative tensor comparisons form a coherent
triangle. -/
@[stacks 09LN "coherence of categorical and ordinary tensor realization comparisons"]
theorem categoricalIso_trans_realizationIso :
    (categoricalIso (R := R) (A := A) (B := B) N).trans
        (realizationIso (R := R) (A := A) (B := B) N) =
      Module.Bimodule.RelativeTensor.realizationIso
        (R := R) (A := A) (B := B) N := sorry

/-- The forward categorical-to-ordinary comparison sends a categorical pure tensor to the
functor-level ordinary pure tensor. -/
@[simp, stacks 09LN "categorical-to-ordinary relative tensor comparison on pure tensors"]
theorem categoricalIso_hom_app_tmul (M : ModuleCat.{u} Aᵐᵒᵖ) (m : M) (n : N) :
    ((categoricalIso (R := R) (A := A) (B := B) N).hom.app M).hom
        (tensorBimodMk (R := R) (A := A) (B := B)
          (M := RightModuleFunctor.restricted (R := R) M) (N := N) (m ⊗ₜ[R] n)) =
      Module.Bimodule.RelativeTensor.Functor.tmul
        (R := R) (A := A) (B := B) m n := sorry

/-- The inverse ordinary-to-categorical comparison sends a functor-level ordinary pure tensor to
its categorical coequalizer class. -/
@[simp, stacks 09LN "ordinary-to-categorical relative tensor comparison on pure tensors"]
theorem categoricalIso_inv_app_tmul (M : ModuleCat.{u} Aᵐᵒᵖ) (m : M) (n : N) :
    ((categoricalIso (R := R) (A := A) (B := B) N).inv.app M).hom
        (Module.Bimodule.RelativeTensor.Functor.tmul
          (R := R) (A := A) (B := B) m n) =
      tensorBimodMk (R := R) (A := A) (B := B)
        (M := RightModuleFunctor.restricted (R := R) M) (N := N) (m ⊗ₜ[R] n) := sorry

end Ordinary

#synth (CategoryTheory.Bimod.tensorRight
  (R := Mon.trivial (ModuleCat.{u} R))
  (toBimod (R := R) (A := A) (B := B) N)).Additive
#synth Functor.Linear R (CategoryTheory.Bimod.tensorRight
  (R := Mon.trivial (ModuleCat.{u} R))
  (toBimod (R := R) (A := A) (B := B) N))
#synth (categoricalFunctor (R := R) (A := A) (B := B) N).Additive
#synth Functor.Linear R (categoricalFunctor (R := R) (A := A) (B := B) N)
#synth (realizationFunctor (R := R) (A := A) (B := B) N).Additive
#synth Functor.Linear R (realizationFunctor (R := R) (A := A) (B := B) N)
#synth (Ordinary.functor (R := R) (A := A) (B := B) N).Additive
#synth Functor.Linear R (Ordinary.functor (R := R) (A := A) (B := B) N)

end Module.Bimodule.RelativeTensor

end
