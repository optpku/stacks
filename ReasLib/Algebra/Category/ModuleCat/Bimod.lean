/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Internal.Module
public import ReasLib.Algebra.Module.Bimodule.Hom
public import ReasLib.CategoryTheory.Monoidal.Bimod.Module.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Algebra bimodules as bimodule objects in `ModuleCat`

This file is the bridge from the concrete algebra-bimodule interface to Mathlib's `Bimod`.
It is deliberately restricted to one universe, matching the monoidal structure on `ModuleCat`.
The concrete layer remains universe-polymorphic and does not depend on this categorical layer.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u

namespace Module.Bimodule

variable {R : Type u} [CommRing R]

/-- An `R`-algebra as the corresponding monoid object in `ModuleCat R`. -/
@[stacks 09LN "ordinary algebra as a module-category monoid"]
noncomputable def algebraMon (A : Type u) [Ring A] [Algebra R A] :
    Mon (ModuleCat.{u} R) :=
  (ModuleCat.monModuleEquivalenceAlgebra (R := R)).inverse.obj (AlgCat.of R A)

/-- The carrier of `algebraMon A` is the `R`-module underlying `A`. -/
@[simp]
theorem algebraMon_X (A : Type u) [Ring A] [Algebra R A] :
    (algebraMon (R := R) A).X = ModuleCat.of R A := sorry

/-- The unit of `algebraMon A` is the algebra map from `R`. -/
@[simp]
theorem algebraMon_one_apply (A : Type u) [Ring A] [Algebra R A] (r : R) :
    (algebraMon (R := R) A).mon.one r = algebraMap R A r := sorry

/-- Multiplication in `algebraMon A` is multiplication in `A`. -/
@[simp]
theorem algebraMon_mul_tmul (A : Type u) [Ring A] [Algebra R A] (a b : A) :
    (algebraMon (R := R) A).mon.mul (a ⊗ₜ[R] b) = a * b := sorry

/-- The base ring, regarded as an algebra over itself, gives the tensor-unit monoid. -/
@[simp]
theorem algebraMon_self :
    algebraMon (R := R) R = Mon.trivial (ModuleCat.{u} R) := sorry

namespace ToBimod

variable {A B N : Type u}
variable [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [AddCommGroup N] [Module R N]

/-- The categorical left action associated to an ordinary left algebra action. -/
def leftAction [Module A N] [IsScalarTower R A N] :
    ModuleCat.of R A ⊗ ModuleCat.of R N ⟶ ModuleCat.of R N :=
  ModuleCat.ofHom (TensorProduct.lift (Algebra.lsmul R R N).toLinearMap)

/-- The categorical left action evaluates as the original scalar action. -/
@[simp]
theorem leftAction_tmul [Module A N] [IsScalarTower R A N] (a : A) (n : N) :
    leftAction (R := R) (A := A) (N := N) (a ⊗ₜ[R] n) = a • n := sorry

/-- The categorical right action associated to an ordinary right algebra action. -/
def rightAction [Module Bᵐᵒᵖ N] [IsScalarTower R Bᵐᵒᵖ N] :
    ModuleCat.of R N ⊗ ModuleCat.of R B ⟶ ModuleCat.of R N :=
  ModuleCat.ofHom <| TensorProduct.lift <|
    ((Algebra.lsmul R R N : Bᵐᵒᵖ →ₐ[R] Module.End R N).toLinearMap.flip).compl₂
      (MulOpposite.opLinearEquiv R).toLinearMap

/-- The categorical right action evaluates as the original opposite-algebra scalar action. -/
@[simp]
theorem rightAction_tmul [Module Bᵐᵒᵖ N] [IsScalarTower R Bᵐᵒᵖ N] (n : N) (b : B) :
    rightAction (R := R) (B := B) (N := N) (n ⊗ₜ[R] b) = MulOpposite.op b • n := sorry

/-- The concrete left action is unital as a `ModuleCat` action. -/
theorem one_actLeft [Module A N] [IsScalarTower R A N] :
    ((algebraMon (R := R) A).mon.one ▷ ModuleCat.of R N) ≫
        leftAction (R := R) (A := A) (N := N) =
      (λ_ (ModuleCat.of R N)).hom := sorry

/-- The concrete left action is associative as a `ModuleCat` action. -/
theorem left_assoc [Module A N] [IsScalarTower R A N] :
    ((algebraMon (R := R) A).mon.mul ▷ ModuleCat.of R N) ≫
        leftAction (R := R) (A := A) (N := N) =
      (α_ (ModuleCat.of R A) (ModuleCat.of R A) (ModuleCat.of R N)).hom ≫
        (ModuleCat.of R A ◁ leftAction (R := R) (A := A) (N := N)) ≫
          leftAction (R := R) (A := A) (N := N) := sorry

/-- The concrete right action is unital as a `ModuleCat` action. -/
theorem actRight_one [Module Bᵐᵒᵖ N] [IsScalarTower R Bᵐᵒᵖ N] :
    (ModuleCat.of R N ◁ (algebraMon (R := R) B).mon.one) ≫
        rightAction (R := R) (B := B) (N := N) =
      (ρ_ (ModuleCat.of R N)).hom := sorry

/-- The concrete right action is associative as a `ModuleCat` action. -/
theorem right_assoc [Module Bᵐᵒᵖ N] [IsScalarTower R Bᵐᵒᵖ N] :
    (ModuleCat.of R N ◁ (algebraMon (R := R) B).mon.mul) ≫
        rightAction (R := R) (B := B) (N := N) =
      (α_ (ModuleCat.of R N) (ModuleCat.of R B) (ModuleCat.of R B)).inv ≫
        (rightAction (R := R) (B := B) (N := N) ▷ ModuleCat.of R B) ≫
          rightAction (R := R) (B := B) (N := N) := sorry

/-- Commuting ordinary scalar actions give the middle associativity law for `Bimod`. -/
theorem middle_assoc [Module A N] [Module Bᵐᵒᵖ N]
    [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N] :
    (leftAction (R := R) (A := A) (N := N) ▷ ModuleCat.of R B) ≫
        rightAction (R := R) (B := B) (N := N) =
      (α_ (ModuleCat.of R A) (ModuleCat.of R N) (ModuleCat.of R B)).hom ≫
        (ModuleCat.of R A ◁ rightAction (R := R) (B := B) (N := N)) ≫
          leftAction (R := R) (A := A) (N := N) := sorry

end ToBimod

variable {A B N N' N'' : Type u}
variable [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/-- An ordinary left-`A`, right-`B` bimodule as Mathlib's categorical bimodule object. -/
@[stacks 09LN "ordinary algebra bimodule as a bimodule object"]
def toBimod (N : Type u) [AddCommGroup N] [Module R N] [Module A N] [Module Bᵐᵒᵖ N]
    [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N] :
    Bimod (algebraMon (R := R) A) (algebraMon (R := R) B) where
  X := ModuleCat.of R N
  actLeft := ToBimod.leftAction (R := R) (A := A) (N := N)
  actRight := ToBimod.rightAction (R := R) (B := B) (N := N)
  one_actLeft := ToBimod.one_actLeft
  left_assoc := ToBimod.left_assoc
  actRight_one := ToBimod.actRight_one
  right_assoc := ToBimod.right_assoc
  middle_assoc := ToBimod.middle_assoc

/-- The carrier of the categorical bimodule associated to `N` is `N` as an `R`-module. -/
@[simp]
theorem toBimod_X [AddCommGroup N] [Module R N] [Module A N] [Module Bᵐᵒᵖ N]
    [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N] :
    (toBimod (R := R) (A := A) (B := B) N).X = ModuleCat.of R N := sorry

/-- The left action of `toBimod` is the action induced by the original `A`-module. -/
@[simp]
theorem toBimod_actLeft [AddCommGroup N] [Module R N] [Module A N] [Module Bᵐᵒᵖ N]
    [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N] :
    (toBimod (R := R) (A := A) (B := B) N).actLeft =
      ToBimod.leftAction (R := R) (A := A) (N := N) := sorry

/-- The right action of `toBimod` is the action induced by the original right `B`-module. -/
@[simp]
theorem toBimod_actRight [AddCommGroup N] [Module R N] [Module A N] [Module Bᵐᵒᵖ N]
    [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N] :
    (toBimod (R := R) (A := A) (B := B) N).actRight =
      ToBimod.rightAction (R := R) (B := B) (N := N) := sorry

/-- An ordinary right `A`-module as a right module over `algebraMon A`. -/
@[stacks 09LN "ordinary right module as a categorical module object"]
def toRightModule (N : Type u) [AddCommGroup N] [Module R N] [Module Aᵐᵒᵖ N]
    [IsScalarTower R Aᵐᵒᵖ N] :
    CategoryTheory.Bimod.RightModule (algebraMon (R := R) A) :=
  toBimod (R := R) (A := R) (B := A) N

/-- The carrier of the categorical right module associated to `N` is `N` as an `R`-module. -/
@[simp]
theorem toRightModule_X [AddCommGroup N] [Module R N] [Module Aᵐᵒᵖ N]
    [IsScalarTower R Aᵐᵒᵖ N] :
    (toRightModule (R := R) (A := A) N).X = ModuleCat.of R N := sorry

/-- The action of `toRightModule` is the categorical form of the original right action. -/
@[simp]
theorem toRightModule_actRight [AddCommGroup N] [Module R N] [Module Aᵐᵒᵖ N]
    [IsScalarTower R Aᵐᵒᵖ N] :
    (toRightModule (R := R) (A := A) N).actRight =
      ToBimod.rightAction (R := R) (B := A) (N := N) := sorry

namespace ToRightModule

variable [AddCommGroup N] [Module R N] [Module Aᵐᵒᵖ N]
variable [IsScalarTower R Aᵐᵒᵖ N]
variable [AddCommGroup N'] [Module R N'] [Module Aᵐᵒᵖ N']
variable [IsScalarTower R Aᵐᵒᵖ N']

/-- A right-linear map as a morphism of categorical right modules. -/
@[stacks 09LN "ordinary right-linear maps as categorical module morphisms"]
def map (f : N →ₗ[Aᵐᵒᵖ] N') :
    toRightModule (R := R) (A := A) N ⟶ toRightModule (R := R) (A := A) N' where
  hom := ModuleCat.ofHom (f.restrictScalars R)
  left_act_hom := sorry
  right_act_hom := sorry

/-- The underlying categorical map is restriction of scalars to `R`. -/
@[simp]
theorem map_hom (f : N →ₗ[Aᵐᵒᵖ] N') :
    (map (R := R) f).hom = ModuleCat.ofHom (f.restrictScalars R) := sorry

/-- The categorical right-module bridge preserves evaluation. -/
@[simp]
theorem map_apply (f : N →ₗ[Aᵐᵒᵖ] N') (n : N) : (map (R := R) f).hom n = f n := sorry

/-- The categorical right-module bridge preserves identity maps. -/
@[simp]
theorem map_id :
    map (R := R) (LinearMap.id : N →ₗ[Aᵐᵒᵖ] N) = 𝟙 (toRightModule (R := R) (A := A) N) := sorry

/-- The categorical right-module bridge preserves composition. -/
@[simp]
theorem map_comp
    [AddCommGroup N''] [Module R N''] [Module Aᵐᵒᵖ N''] [IsScalarTower R Aᵐᵒᵖ N'']
    (f : N →ₗ[Aᵐᵒᵖ] N') (g : N' →ₗ[Aᵐᵒᵖ] N'') :
    map (R := R) (g.comp f) = map (R := R) f ≫ map (R := R) g := sorry

namespace OfHom

variable (f : toRightModule (R := R) (A := A) N ⟶ toRightModule (R := R) (A := A) N')

/-- The underlying `R`-linear map of a morphism between internalized right modules. -/
def moduleHom : N →ₗ[R] N' := f.hom.hom

/-- The underlying map of a categorical right-module morphism preserves the right action. -/
theorem map_smul (a : Aᵐᵒᵖ) (n : N) : moduleHom f (a • n) = a • moduleHom f n := sorry

end OfHom

/-- Recover the ordinary right-linear map underlying a categorical right-module morphism. -/
def ofHom
    (f : toRightModule (R := R) (A := A) N ⟶ toRightModule (R := R) (A := A) N') :
    N →ₗ[Aᵐᵒᵖ] N' where
  toFun := OfHom.moduleHom f
  map_add' := (OfHom.moduleHom f).map_add
  map_smul' := OfHom.map_smul f

/-- Recovering a right-linear map from a categorical morphism preserves evaluation. -/
@[simp]
theorem ofHom_apply
    (f : toRightModule (R := R) (A := A) N ⟶ toRightModule (R := R) (A := A) N')
    (n : N) : ofHom f n = f.hom n := sorry

/-- Ordinary right-linear maps and morphisms of their categorical modules are equivalent. -/
@[stacks 09LN "ordinary and categorical right-module morphisms"]
def homEquiv :
    (N →ₗ[Aᵐᵒᵖ] N') ≃
      (toRightModule (R := R) (A := A) N ⟶ toRightModule (R := R) (A := A) N') where
  toFun := map (R := R)
  invFun := ofHom
  left_inv := sorry
  right_inv := sorry

/-- Applying `homEquiv` is the ordinary-to-categorical map conversion. -/
@[simp]
theorem homEquiv_apply (f : N →ₗ[Aᵐᵒᵖ] N') : homEquiv (R := R) f = map (R := R) f := sorry

/-- Applying the inverse of `homEquiv` recovers the underlying ordinary right-linear map. -/
@[simp]
theorem homEquiv_symm_apply
    (f : toRightModule (R := R) (A := A) N ⟶ toRightModule (R := R) (A := A) N') :
    (homEquiv (R := R)).symm f = ofHom f := sorry

/-- Internalizing a right-linear map and recovering it returns the original map. -/
@[simp]
theorem ofHom_map (f : N →ₗ[Aᵐᵒᵖ] N') : ofHom (map (R := R) f) = f := sorry

/-- Recovering and then internalizing a categorical right-module morphism returns it. -/
@[simp]
theorem map_ofHom
    (f : toRightModule (R := R) (A := A) N ⟶ toRightModule (R := R) (A := A) N') :
    map (R := R) (ofHom f) = f := sorry

/-- Recovering the categorical identity gives the ordinary identity linear map. -/
@[simp]
theorem ofHom_id :
    ofHom (𝟙 (toRightModule (R := R) (A := A) N)) =
      (LinearMap.id : N →ₗ[Aᵐᵒᵖ] N) := sorry

/-- Recovering a categorical composite gives the composite ordinary right-linear map. -/
@[simp]
theorem ofHom_comp
    [AddCommGroup N''] [Module R N''] [Module Aᵐᵒᵖ N''] [IsScalarTower R Aᵐᵒᵖ N'']
    (f : toRightModule (R := R) (A := A) N ⟶ toRightModule (R := R) (A := A) N')
    (g : toRightModule (R := R) (A := A) N' ⟶ toRightModule (R := R) (A := A) N'') :
    ofHom (f ≫ g) = (ofHom g).comp (ofHom f) := sorry

end ToRightModule

namespace ToLeftModule

/-- The tensor-unit right action satisfies the right unit law. -/
theorem actRight_one (N : Type u) [AddCommGroup N] [Module R N] :
    (ModuleCat.of R N ◁ (Mon.trivial (ModuleCat R)).mon.one) ≫
        (ρ_ (ModuleCat.of R N)).hom =
      (ρ_ (ModuleCat.of R N)).hom := sorry

/-- The tensor-unit right action satisfies the right associativity law. -/
theorem right_assoc (N : Type u) [AddCommGroup N] [Module R N] :
    (ModuleCat.of R N ◁ (Mon.trivial (ModuleCat R)).mon.mul) ≫
        (ρ_ (ModuleCat.of R N)).hom =
      (α_ (ModuleCat.of R N) (Mon.trivial (ModuleCat R)).X
        (Mon.trivial (ModuleCat R)).X).inv ≫
        ((ρ_ (ModuleCat.of R N)).hom ▷ (Mon.trivial (ModuleCat R)).X) ≫
          (ρ_ (ModuleCat.of R N)).hom := sorry

/-- The concrete left action commutes with the tensor-unit right action. -/
theorem middle_assoc (N : Type u) [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] :
    (ToBimod.leftAction (R := R) (A := A) (N := N) ▷
        (Mon.trivial (ModuleCat R)).X) ≫ (ρ_ (ModuleCat.of R N)).hom =
      (α_ (algebraMon (R := R) A).X (ModuleCat.of R N)
        (Mon.trivial (ModuleCat R)).X).hom ≫
        ((algebraMon (R := R) A).X ◁ (ρ_ (ModuleCat.of R N)).hom) ≫
          ToBimod.leftAction (R := R) (A := A) (N := N) := sorry

end ToLeftModule

/-- An ordinary left `A`-module as a left module over `algebraMon A`. -/
@[stacks 09LN "ordinary left module as a categorical module object"]
def toLeftModule (N : Type u) [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] :
    CategoryTheory.Bimod.LeftModule (algebraMon (R := R) A) where
  X := ModuleCat.of R N
  actLeft := ToBimod.leftAction (R := R) (A := A) (N := N)
  actRight := (ρ_ (ModuleCat.of R N)).hom
  one_actLeft := ToBimod.one_actLeft
  left_assoc := ToBimod.left_assoc
  actRight_one := ToLeftModule.actRight_one (R := R) N
  right_assoc := ToLeftModule.right_assoc (R := R) N
  middle_assoc := ToLeftModule.middle_assoc (R := R) (A := A) N

/-- The carrier of the categorical left module associated to `N` is `N` as an `R`-module. -/
@[simp]
theorem toLeftModule_X [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N] :
    (toLeftModule (R := R) (A := A) N).X = ModuleCat.of R N := sorry

/-- The action of `toLeftModule` is the categorical form of the original left action. -/
@[simp]
theorem toLeftModule_actLeft [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] :
    (toLeftModule (R := R) (A := A) N).actLeft =
      ToBimod.leftAction (R := R) (A := A) (N := N) := sorry

namespace ToLeftModule

variable [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
variable [AddCommGroup N'] [Module R N'] [Module A N'] [IsScalarTower R A N']

/-- A left-linear map as a morphism of categorical left modules. -/
@[stacks 09LN "ordinary left-linear maps as categorical module morphisms"]
def map (f : N →ₗ[A] N') :
    toLeftModule (R := R) (A := A) N ⟶ toLeftModule (R := R) (A := A) N' where
  hom := ModuleCat.ofHom (f.restrictScalars R)
  left_act_hom := sorry
  right_act_hom := sorry

/-- The underlying categorical map is restriction of scalars to `R`. -/
@[simp]
theorem map_hom (f : N →ₗ[A] N') :
    (map (R := R) f).hom = ModuleCat.ofHom (f.restrictScalars R) := sorry

/-- The categorical left-module bridge preserves evaluation. -/
@[simp]
theorem map_apply (f : N →ₗ[A] N') (n : N) : (map (R := R) f).hom n = f n := sorry

/-- The categorical left-module bridge preserves identity maps. -/
@[simp]
theorem map_id :
    map (R := R) (LinearMap.id : N →ₗ[A] N) = 𝟙 (toLeftModule (R := R) (A := A) N) := sorry

/-- The categorical left-module bridge preserves composition. -/
@[simp]
theorem map_comp [AddCommGroup N''] [Module R N''] [Module A N''] [IsScalarTower R A N'']
    (f : N →ₗ[A] N') (g : N' →ₗ[A] N'') :
    map (R := R) (g.comp f) = map (R := R) f ≫ map (R := R) g := sorry

namespace OfHom

variable (f : toLeftModule (R := R) (A := A) N ⟶ toLeftModule (R := R) (A := A) N')

/-- The underlying `R`-linear map of a morphism between internalized left modules. -/
def moduleHom : N →ₗ[R] N' := f.hom.hom

/-- The underlying map of a categorical left-module morphism preserves the left action. -/
theorem map_smul (a : A) (n : N) : moduleHom f (a • n) = a • moduleHom f n := sorry

end OfHom

/-- Recover the ordinary left-linear map underlying a categorical left-module morphism. -/
def ofHom
    (f : toLeftModule (R := R) (A := A) N ⟶ toLeftModule (R := R) (A := A) N') :
    N →ₗ[A] N' where
  toFun := OfHom.moduleHom f
  map_add' := (OfHom.moduleHom f).map_add
  map_smul' := OfHom.map_smul f

/-- Recovering a left-linear map from a categorical morphism preserves evaluation. -/
@[simp]
theorem ofHom_apply
    (f : toLeftModule (R := R) (A := A) N ⟶ toLeftModule (R := R) (A := A) N')
    (n : N) : ofHom f n = f.hom n := sorry

/-- Ordinary left-linear maps and morphisms of their categorical modules are equivalent. -/
@[stacks 09LN "ordinary and categorical left-module morphisms"]
def homEquiv :
    (N →ₗ[A] N') ≃
      (toLeftModule (R := R) (A := A) N ⟶ toLeftModule (R := R) (A := A) N') where
  toFun := map (R := R)
  invFun := ofHom
  left_inv := sorry
  right_inv := sorry

/-- Applying `homEquiv` is the ordinary-to-categorical map conversion. -/
@[simp]
theorem homEquiv_apply (f : N →ₗ[A] N') : homEquiv (R := R) f = map (R := R) f := sorry

/-- Applying the inverse of `homEquiv` recovers the underlying ordinary left-linear map. -/
@[simp]
theorem homEquiv_symm_apply
    (f : toLeftModule (R := R) (A := A) N ⟶ toLeftModule (R := R) (A := A) N') :
    (homEquiv (R := R)).symm f = ofHom f := sorry

/-- Internalizing a left-linear map and recovering it returns the original map. -/
@[simp]
theorem ofHom_map (f : N →ₗ[A] N') : ofHom (map (R := R) f) = f := sorry

/-- Recovering and then internalizing a categorical left-module morphism returns it. -/
@[simp]
theorem map_ofHom
    (f : toLeftModule (R := R) (A := A) N ⟶ toLeftModule (R := R) (A := A) N') :
    map (R := R) (ofHom f) = f := sorry

/-- Recovering the categorical identity gives the ordinary identity linear map. -/
@[simp]
theorem ofHom_id :
    ofHom (𝟙 (toLeftModule (R := R) (A := A) N)) =
      (LinearMap.id : N →ₗ[A] N) := sorry

/-- Recovering a categorical composite gives the composite ordinary left-linear map. -/
@[simp]
theorem ofHom_comp [AddCommGroup N''] [Module R N''] [Module A N''] [IsScalarTower R A N'']
    (f : toLeftModule (R := R) (A := A) N ⟶ toLeftModule (R := R) (A := A) N')
    (g : toLeftModule (R := R) (A := A) N' ⟶ toLeftModule (R := R) (A := A) N'') :
    ofHom (f ≫ g) = (ofHom g).comp (ofHom f) := sorry

end ToLeftModule

namespace Hom

variable [AddCommGroup N] [Module R N] [Module A N] [Module Bᵐᵒᵖ N]
variable [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
variable [AddCommGroup N'] [Module R N'] [Module A N'] [Module Bᵐᵒᵖ N']
variable [IsScalarTower R A N'] [IsScalarTower R Bᵐᵒᵖ N'] [SMulCommClass A Bᵐᵒᵖ N']

namespace ToBimod

/-- The underlying `R`-linear map of a concrete bimodule morphism, bundled in `ModuleCat`. -/
def moduleHom (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    ModuleCat.of R N ⟶ ModuleCat.of R N' :=
  ModuleCat.ofHom ((Hom.toRightLinearMap f).restrictScalars R)

/-- The underlying `ModuleCat` morphism preserves the internal left action. -/
theorem left_act_hom (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    (Module.Bimodule.toBimod (R := R) (A := A) (B := B) N).actLeft ≫ moduleHom f =
      ((algebraMon (R := R) A).X ◁ moduleHom f) ≫
        (Module.Bimodule.toBimod (R := R) (A := A) (B := B) N').actLeft := sorry

/-- The underlying `ModuleCat` morphism preserves the internal right action. -/
theorem right_act_hom (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    (Module.Bimodule.toBimod (R := R) (A := A) (B := B) N).actRight ≫ moduleHom f =
      (moduleHom f ▷ (algebraMon (R := R) B).X) ≫
        (Module.Bimodule.toBimod (R := R) (A := A) (B := B) N').actRight := sorry

end ToBimod

/-- A concrete bimodule morphism as a morphism of categorical bimodule objects. -/
def toBimod (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    Module.Bimodule.toBimod (R := R) (A := A) (B := B) N ⟶
      Module.Bimodule.toBimod (R := R) (A := A) (B := B) N' where
  hom := ToBimod.moduleHom f
  left_act_hom := ToBimod.left_act_hom f
  right_act_hom := ToBimod.right_act_hom f

/-- The underlying categorical morphism of `f.toBimod` is the restricted scalar map. -/
@[simp]
theorem toBimod_hom (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    (toBimod f).hom = ToBimod.moduleHom f := sorry

/-- The categorical bridge preserves evaluation of a concrete bimodule morphism. -/
@[simp]
theorem toBimod_apply (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) (n : N) :
    (toBimod f).hom n = f n := sorry

namespace OfBimod

variable (f : Module.Bimodule.toBimod (R := R) (A := A) (B := B) N ⟶
  Module.Bimodule.toBimod (R := R) (A := A) (B := B) N')

/-- The underlying `R`-linear map of a morphism between internalized concrete bimodules. -/
def moduleHom : N →ₗ[R] N' := f.hom.hom

/-- The underlying function of an internal bimodule morphism is additive. -/
theorem map_add (x y : N) : moduleHom f (x + y) = moduleHom f x + moduleHom f y := sorry

/-- The underlying function of an internal bimodule morphism preserves the right action. -/
theorem map_right_smul (b : Bᵐᵒᵖ) (n : N) :
    moduleHom f (b • n) = b • moduleHom f n := sorry

/-- The right-linear map underlying a morphism between internalized concrete bimodules. -/
def linearMap : N →ₗ[Bᵐᵒᵖ] N' where
  toFun := moduleHom f
  map_add' := map_add f
  map_smul' := map_right_smul f

/-- The right-linear map underlying an internal bimodule morphism preserves the left action. -/
theorem map_left_smul (a : A) (n : N) : linearMap f (a • n) = a • linearMap f n := sorry

end OfBimod

/-- A categorical bimodule morphism as a concrete bimodule morphism. -/
def ofBimod
    (f : Module.Bimodule.toBimod (R := R) (A := A) (B := B) N ⟶
      Module.Bimodule.toBimod (R := R) (A := A) (B := B) N') :
    Hom (R := R) (A := A) (B := B) (N := N) (N' := N') :=
  ⟨OfBimod.linearMap f, OfBimod.map_left_smul f⟩

/-- The right-linear map of `ofBimod f` is its explicitly reconstructed linear map. -/
@[simp]
theorem ofBimod_toRightLinearMap
    (f : Module.Bimodule.toBimod (R := R) (A := A) (B := B) N ⟶
      Module.Bimodule.toBimod (R := R) (A := A) (B := B) N') :
    Hom.toRightLinearMap (ofBimod f) = OfBimod.linearMap f := sorry

/-- Recovering a concrete morphism from a categorical morphism preserves evaluation. -/
@[simp]
theorem ofBimod_apply
    (f : Module.Bimodule.toBimod (R := R) (A := A) (B := B) N ⟶
      Module.Bimodule.toBimod (R := R) (A := A) (B := B) N') (n : N) :
    ofBimod f n = f.hom n := sorry

/-- Concrete and categorical morphisms between ordinary bimodules are canonically equivalent. -/
@[stacks 09LN "ordinary and categorical bimodule morphisms"]
def bimodEquiv :
    Hom (R := R) (A := A) (B := B) (N := N) (N' := N') ≃
      (Module.Bimodule.toBimod (R := R) (A := A) (B := B) N ⟶
        Module.Bimodule.toBimod (R := R) (A := A) (B := B) N') where
  toFun := toBimod
  invFun := ofBimod
  left_inv := sorry
  right_inv := sorry

/-- Applying `bimodEquiv` is the concrete-to-categorical conversion. -/
@[simp]
theorem bimodEquiv_apply
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    bimodEquiv f = toBimod f := sorry

/-- Applying the inverse of `bimodEquiv` is the categorical-to-concrete conversion. -/
@[simp]
theorem bimodEquiv_symm_apply
    (f : Module.Bimodule.toBimod (R := R) (A := A) (B := B) N ⟶
      Module.Bimodule.toBimod (R := R) (A := A) (B := B) N') :
    bimodEquiv.symm f = ofBimod f := sorry

/-- Converting a concrete bimodule morphism to the categorical model and back is the identity. -/
@[simp]
theorem ofBimod_toBimod
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    ofBimod (toBimod f) = f := sorry

/-- Converting a categorical bimodule morphism to the concrete model and back is the identity. -/
@[simp]
theorem toBimod_ofBimod
    (f : Module.Bimodule.toBimod (R := R) (A := A) (B := B) N ⟶
      Module.Bimodule.toBimod (R := R) (A := A) (B := B) N') :
    toBimod (ofBimod f) = f := sorry

/-- The categorical bridge sends the concrete identity to the categorical identity. -/
@[simp]
theorem toBimod_id :
    toBimod (id (R := R) (A := A) (B := B) (N := N)) =
      𝟙 (Module.Bimodule.toBimod (R := R) (A := A) (B := B) N) := sorry

/-- The categorical bridge preserves composition. -/
@[simp]
theorem toBimod_comp
    [AddCommGroup N''] [Module R N''] [Module A N''] [Module Bᵐᵒᵖ N'']
    [IsScalarTower R A N''] [IsScalarTower R Bᵐᵒᵖ N''] [SMulCommClass A Bᵐᵒᵖ N'']
    (g : Hom (R := R) (A := A) (B := B) (N := N') (N' := N''))
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    toBimod (comp g f) = toBimod f ≫ toBimod g := sorry

/-- The concrete bridge sends the categorical identity to the concrete identity. -/
@[simp]
theorem ofBimod_id :
    ofBimod (𝟙 (Module.Bimodule.toBimod (R := R) (A := A) (B := B) N)) =
      id (R := R) (A := A) (B := B) (N := N) := sorry

/-- The concrete bridge preserves categorical composition. -/
@[simp]
theorem ofBimod_comp
    [AddCommGroup N''] [Module R N''] [Module A N''] [Module Bᵐᵒᵖ N'']
    [IsScalarTower R A N''] [IsScalarTower R Bᵐᵒᵖ N''] [SMulCommClass A Bᵐᵒᵖ N'']
    (f : Module.Bimodule.toBimod (R := R) (A := A) (B := B) N ⟶
      Module.Bimodule.toBimod (R := R) (A := A) (B := B) N')
    (g : Module.Bimodule.toBimod (R := R) (A := A) (B := B) N' ⟶
      Module.Bimodule.toBimod (R := R) (A := A) (B := B) N'') :
    ofBimod (f ≫ g) = comp (ofBimod g) (ofBimod f) := sorry

end Hom

end Module.Bimodule
