/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Bimod.Functor
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Restrict
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ordinary modules and categorical module objects

This file identifies ordinary one-sided modules with categorical module objects over the
corresponding algebra object.  The inverse functors extract the ordinary scalar action directly
from the categorical action, and the unit and counit record the resulting canonical
equivalences.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u

namespace Module.Bimodule

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]

namespace RightModuleFunctor.Inverse

variable (M : Bimod.RightModule (algebraMon (R := R) A))

/-- The right action of a categorical right module, read as an ordinary `Aᵐᵒᵖ`-action. -/
@[stacks 09LN "ordinary action extracted from a categorical right module"]
def smul (a : Aᵐᵒᵖ) (x : M.X) : M.X :=
  M.actRight.hom (x ⊗ₜ[R] a.unop)

/-- The scalar-action structure underlying the ordinary module extracted from a categorical
right module. -/
@[implicit_reducible, stacks 09LN "scalar action extracted from a categorical right module"]
def smulStruct : SMul Aᵐᵒᵖ M.X :=
  ⟨smul (R := R) M⟩

/-- The extracted right action is unital. -/
@[stacks 09LN "unit law for the extracted right action"]
theorem one_smul (x : M.X) : smul (R := R) M 1 x = x := sorry

/-- The extracted right action is associative as an `Aᵐᵒᵖ`-action. -/
@[stacks 09LN "associativity of the extracted right action"]
theorem mul_smul (a b : Aᵐᵒᵖ) (x : M.X) :
    smul (R := R) M (a * b) x = smul (R := R) M a (smul (R := R) M b x) := sorry

/-- The extracted right action preserves zero in the module variable. -/
@[stacks 09LN "zero law for the extracted right action"]
theorem smul_zero (a : Aᵐᵒᵖ) : smul (R := R) M a 0 = 0 := sorry

/-- The extracted right action preserves addition in the module variable. -/
@[stacks 09LN "additivity of the extracted right action"]
theorem smul_add (a : Aᵐᵒᵖ) (x y : M.X) :
    smul (R := R) M a (x + y) = smul (R := R) M a x + smul (R := R) M a y := sorry

/-- The extracted right action is additive in its scalar variable. -/
@[stacks 09LN "scalar additivity of the extracted right action"]
theorem add_smul (a b : Aᵐᵒᵖ) (x : M.X) :
    smul (R := R) M (a + b) x = smul (R := R) M a x + smul (R := R) M b x := sorry

/-- The zero scalar acts by zero under the extracted right action. -/
@[stacks 09LN "zero scalar law for the extracted right action"]
theorem zero_smul (x : M.X) : smul (R := R) M 0 x = 0 := sorry

/-- The ordinary right `A`-module structure extracted from a categorical right module. -/
@[implicit_reducible, stacks 09LN "ordinary module extracted from a categorical right module"]
def module : Module Aᵐᵒᵖ M.X where
  smul := (smulStruct (R := R) M).smul
  one_smul := one_smul (R := R) M
  mul_smul := mul_smul (R := R) M
  smul_zero := smul_zero (R := R) M
  smul_add := smul_add (R := R) M
  add_smul := add_smul (R := R) M
  zero_smul := zero_smul (R := R) M

/-- The ordinary module-category object extracted from a categorical right module. -/
@[stacks 09LN "ordinary object extracted from a categorical right module"]
def obj : ModuleCat.{u} Aᵐᵒᵖ :=
  @ModuleCat.of Aᵐᵒᵖ _ M.X inferInstance (module (R := R) M)

/-- Scalar multiplication in the extracted ordinary object evaluates the categorical right
action. -/
@[simp, stacks 09LN "scalar action in the extracted ordinary right module"]
theorem obj_smul (a : Aᵐᵒᵖ) (x : obj (R := R) M) :
    a • x = M.actRight.hom (x ⊗ₜ[R] a.unop) := sorry

/-- The ground-ring action and the extracted `Aᵐᵒᵖ`-action form the canonical scalar tower. -/
@[stacks 09LN "scalar tower for an extracted ordinary right module"]
theorem isScalarTower :
    @IsScalarTower R Aᵐᵒᵖ M.X Algebra.toSMul (smulStruct (R := R) M)
      inferInstance := sorry

/-- Ground scalars commute with the extracted right action. -/
@[stacks 09LN "ground scalar associativity of the extracted right action"]
theorem smul_assoc (r : R) (a : Aᵐᵒᵖ) (x : M.X) :
    smul (R := R) M (r • a) x = r • smul (R := R) M a x := sorry

/-- Restricting the extracted right action along `algebraMap R Aᵐᵒᵖ` recovers the original
ground-ring action. -/
@[simp, stacks 09LN "ground scalar action in an extracted ordinary right module"]
theorem algebraMap_smul (r : R) (x : M.X) :
    smul (R := R) M (algebraMap R Aᵐᵒᵖ r) x = r • x := sorry

variable {M}
variable {N : Bimod.RightModule (algebraMon (R := R) A)}

/-- The ordinary right-linear map underlying a categorical right-module morphism. -/
@[stacks 09LN "ordinary map extracted from a categorical right-module morphism"]
def linearMap (f : M ⟶ N) :
    @LinearMap Aᵐᵒᵖ Aᵐᵒᵖ _ _ (RingHom.id Aᵐᵒᵖ) M.X N.X inferInstance
      inferInstance (module (R := R) M) (module (R := R) N) :=
  @LinearMap.mk Aᵐᵒᵖ Aᵐᵒᵖ _ _ (RingHom.id Aᵐᵒᵖ) M.X N.X inferInstance
    inferInstance (module (R := R) M) (module (R := R) N)
    f.hom.hom.toAddHom sorry

/-- The extracted ordinary right-linear map is pointwise the original categorical map. -/
@[simp, stacks 09LN "evaluation of an extracted ordinary right-linear map"]
theorem linearMap_apply (f : M ⟶ N) (x : M.X) :
    linearMap (R := R) f x = f.hom x := sorry

/-- The ordinary module-category morphism underlying a categorical right-module morphism. -/
@[stacks 09LN "ordinary morphism extracted from a categorical right-module morphism"]
def map (f : M ⟶ N) : obj (R := R) M ⟶ obj (R := R) N :=
  @ModuleCat.ofHom Aᵐᵒᵖ _ M.X N.X inferInstance (module (R := R) M)
    inferInstance (module (R := R) N) (linearMap (R := R) f)

/-- The underlying linear map of an extracted ordinary morphism is `linearMap f`. -/
@[simp, stacks 09LN "underlying map of an extracted ordinary right-module morphism"]
theorem map_hom (f : M ⟶ N) :
    (map (R := R) f).hom = linearMap (R := R) f := sorry

/-- The extracted ordinary module-category morphism is pointwise the original categorical
map. -/
@[simp, stacks 09LN "evaluation of an extracted ordinary right-module morphism"]
theorem map_apply (f : M ⟶ N) (x : M.X) :
    map (R := R) f x = f.hom x := sorry

/-- Extracting ordinary right modules from categorical right modules defines a functor. -/
@[stacks 09LN "ordinary right-module extraction functor"]
def functor :
    Bimod.RightModule (algebraMon (R := R) A) ⥤ ModuleCat.{u} Aᵐᵒᵖ where
  obj := obj (R := R)
  map := map (R := R)
  map_id := sorry
  map_comp := sorry

/-- The extraction functor returns the explicitly extracted ordinary object. -/
@[simp, stacks 09LN "ordinary right-module extraction on objects"]
theorem functor_obj (M : Bimod.RightModule (algebraMon (R := R) A)) :
    (functor (R := R) (A := A)).obj M = obj (R := R) M := sorry

/-- The extraction functor maps a categorical morphism by its extracted ordinary map. -/
@[simp, stacks 09LN "ordinary right-module extraction on morphisms"]
theorem functor_map {M N : Bimod.RightModule (algebraMon (R := R) A)} (f : M ⟶ N) :
    (functor (R := R) (A := A)).map f = map (R := R) f := sorry

variable (P : ModuleCat.{u} Aᵐᵒᵖ)

/-- The objectwise unit identifying an ordinary right module with realization followed by
extraction. -/
@[stacks 09LN "unit of ordinary right-module realization and extraction"]
def unitApp :
    P ≅ obj (R := R) ((rightModuleFunctor (R := R) (A := A)).obj P) where
  hom := @ModuleCat.ofHom Aᵐᵒᵖ _ P
    ((rightModuleFunctor (R := R) (A := A)).obj P).X inferInstance inferInstance
    inferInstance (module (R := R) ((rightModuleFunctor (R := R) (A := A)).obj P))
    (@LinearMap.mk Aᵐᵒᵖ Aᵐᵒᵖ _ _ (RingHom.id Aᵐᵒᵖ) P
      ((rightModuleFunctor (R := R) (A := A)).obj P).X inferInstance inferInstance
      inferInstance (module (R := R) ((rightModuleFunctor (R := R) (A := A)).obj P))
      (𝟙 P : P ⟶ P).hom.toAddHom sorry)
  inv := @ModuleCat.ofHom Aᵐᵒᵖ _
    ((rightModuleFunctor (R := R) (A := A)).obj P).X P inferInstance
    (module (R := R) ((rightModuleFunctor (R := R) (A := A)).obj P))
    inferInstance inferInstance
    (@LinearMap.mk Aᵐᵒᵖ Aᵐᵒᵖ _ _ (RingHom.id Aᵐᵒᵖ)
      ((rightModuleFunctor (R := R) (A := A)).obj P).X P inferInstance inferInstance
      (module (R := R) ((rightModuleFunctor (R := R) (A := A)).obj P))
      inferInstance (𝟙 P : P ⟶ P).hom.toAddHom sorry)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward unit comparison is the identity on elements. -/
@[simp, stacks 09LN "forward unit of ordinary right-module realization on elements"]
theorem unitApp_hom_apply (x : P) : (unitApp (R := R) P).hom x = x := sorry

/-- The inverse unit comparison is the identity on elements. -/
@[simp, stacks 09LN "inverse unit of ordinary right-module realization on elements"]
theorem unitApp_inv_apply
    (x : obj (R := R) ((rightModuleFunctor (R := R) (A := A)).obj P)) :
    (unitApp (R := R) P).inv x = x := sorry

/-- The objectwise unit comparison is natural in the ordinary right module. -/
@[reassoc, stacks 09LN "naturality of the ordinary right-module realization unit"]
theorem unitApp_naturality {P Q : ModuleCat.{u} Aᵐᵒᵖ} (f : P ⟶ Q) :
    f ≫ (unitApp (R := R) Q).hom =
      (unitApp (R := R) P).hom ≫
        (rightModuleFunctor (R := R) (A := A) ⋙ functor (R := R) (A := A)).map f := sorry

/-- The unit natural isomorphism for ordinary right-module realization and extraction. -/
@[stacks 09LN "unit isomorphism for ordinary right-module realization"]
def unitIso :
    𝟭 (ModuleCat.{u} Aᵐᵒᵖ) ≅
      rightModuleFunctor (R := R) (A := A) ⋙ functor (R := R) (A := A) :=
  NatIso.ofComponents (unitApp (R := R)) (fun f ↦ unitApp_naturality (R := R) f)

variable (M)

/-- The underlying ground-ring comparison for extraction followed by realization. -/
@[stacks 09LN "underlying counit of ordinary right-module realization"]
def counitUnderlyingIso :
    (ModuleCat.restrictScalars (algebraMap R Aᵐᵒᵖ)).obj (obj (R := R) M) ≅ M.X :=
  @ModuleCat.RestrictScalars.identityIso R Aᵐᵒᵖ _ _ _ M.X inferInstance
    inferInstance (module (R := R) M) (isScalarTower (R := R) M)

/-- The objectwise counit identifying extraction followed by realization with the original
categorical right module. -/
@[stacks 09LN "counit of ordinary right-module realization and extraction"]
def counitApp :
    (rightModuleFunctor (R := R) (A := A)).obj (obj (R := R) M) ≅ M :=
  Bimod.isoOfIso (counitUnderlyingIso (R := R) M) sorry sorry

/-- The forward counit comparison is the identity on elements. -/
@[simp, stacks 09LN "forward counit of ordinary right-module realization on elements"]
theorem counitApp_hom_apply
    (x : ((rightModuleFunctor (R := R) (A := A)).obj (obj (R := R) M)).X) :
    (counitApp (R := R) M).hom.hom x = x := sorry

/-- The inverse counit comparison is the identity on elements. -/
@[simp, stacks 09LN "inverse counit of ordinary right-module realization on elements"]
theorem counitApp_inv_apply (x : M.X) :
    (counitApp (R := R) M).inv.hom x = x := sorry

/-- The objectwise counit comparison is natural in the categorical right module. -/
@[reassoc, stacks 09LN "naturality of the ordinary right-module realization counit"]
theorem counitApp_naturality
    {M N : Bimod.RightModule (algebraMon (R := R) A)} (f : M ⟶ N) :
    (functor (R := R) (A := A) ⋙ rightModuleFunctor (R := R) (A := A)).map f ≫
        (counitApp (R := R) N).hom =
      (counitApp (R := R) M).hom ≫ f := sorry

/-- The counit natural isomorphism for ordinary right-module extraction and realization. -/
@[stacks 09LN "counit isomorphism for ordinary right-module realization"]
def counitIso :
    functor (R := R) (A := A) ⋙ rightModuleFunctor (R := R) (A := A) ≅
      𝟭 (Bimod.RightModule (algebraMon (R := R) A)) :=
  NatIso.ofComponents (counitApp (R := R)) (fun f ↦ counitApp_naturality (R := R) f)

/-- The unit and counit comparisons satisfy the realization-side triangle identity. -/
@[stacks 09LN "triangle identity for ordinary right-module realization"]
theorem equivalence_triangle (P : ModuleCat.{u} Aᵐᵒᵖ) :
    (rightModuleFunctor (R := R) (A := A)).map ((unitIso (R := R) (A := A)).hom.app P) ≫
        (counitIso (R := R) (A := A)).hom.app
          ((rightModuleFunctor (R := R) (A := A)).obj P) =
      𝟙 ((rightModuleFunctor (R := R) (A := A)).obj P) := sorry

end RightModuleFunctor.Inverse

/-- Ordinary right `A`-modules and categorical right modules over `algebraMon A` are
canonically equivalent. -/
@[stacks 09LN "ordinary and categorical right modules are equivalent"]
def rightModuleEquivalence :
    ModuleCat.{u} Aᵐᵒᵖ ≌ Bimod.RightModule (algebraMon (R := R) A) :=
  CategoryTheory.Equivalence.mk'
    (rightModuleFunctor (R := R) (A := A))
    (RightModuleFunctor.Inverse.functor (R := R) (A := A))
    (RightModuleFunctor.Inverse.unitIso (R := R) (A := A))
    (RightModuleFunctor.Inverse.counitIso (R := R) (A := A))
    (RightModuleFunctor.Inverse.equivalence_triangle (R := R) (A := A))

/-- The forward functor of `rightModuleEquivalence` is ordinary realization. -/
@[simp, stacks 09LN "forward functor of the ordinary right-module equivalence"]
theorem rightModuleEquivalence_functor :
    (rightModuleEquivalence (R := R) (A := A)).functor =
      rightModuleFunctor (R := R) (A := A) := sorry

/-- The inverse functor of `rightModuleEquivalence` extracts the ordinary module action. -/
@[simp, stacks 09LN "inverse functor of the ordinary right-module equivalence"]
theorem rightModuleEquivalence_inverse :
    (rightModuleEquivalence (R := R) (A := A)).inverse =
      RightModuleFunctor.Inverse.functor (R := R) (A := A) := sorry

namespace RightModuleFunctor.Inverse

/-- The ordinary right-module extraction functor is fully faithful. -/
@[stacks 09LN "ordinary right-module extraction is fully faithful"]
noncomputable def fullyFaithful :
    (functor (R := R) (A := A)).FullyFaithful :=
  (rightModuleEquivalence (R := R) (A := A)).fullyFaithfulInverse

/-- Typeclass search recognizes ordinary right-module extraction as full. -/
@[stacks 09LN "ordinary right-module extraction is full"]
instance functorFull : (functor (R := R) (A := A)).Full := sorry

/-- Typeclass search recognizes ordinary right-module extraction as faithful. -/
@[stacks 09LN "ordinary right-module extraction is faithful"]
instance functorFaithful : (functor (R := R) (A := A)).Faithful := sorry

end RightModuleFunctor.Inverse

namespace RightModuleEquivalence

/-- The forward unit component of the ordinary right-module equivalence is the explicit unit
comparison. -/
@[simp, stacks 09LN "forward unit component of the ordinary right-module equivalence"]
theorem unitIso_hom_app (P : ModuleCat.{u} Aᵐᵒᵖ) :
    (rightModuleEquivalence (R := R) (A := A)).unitIso.hom.app P =
      (RightModuleFunctor.Inverse.unitApp (R := R) P).hom := sorry

/-- The inverse unit component of the ordinary right-module equivalence is the explicit unit
comparison. -/
@[simp, stacks 09LN "inverse unit component of the ordinary right-module equivalence"]
theorem unitIso_inv_app (P : ModuleCat.{u} Aᵐᵒᵖ) :
    (rightModuleEquivalence (R := R) (A := A)).unitIso.inv.app P =
      (RightModuleFunctor.Inverse.unitApp (R := R) P).inv := sorry

/-- The forward counit component of the ordinary right-module equivalence is the explicit counit
comparison. -/
@[simp, stacks 09LN "forward counit component of the ordinary right-module equivalence"]
theorem counitIso_hom_app (M : Bimod.RightModule (algebraMon (R := R) A)) :
    (rightModuleEquivalence (R := R) (A := A)).counitIso.hom.app M =
      (RightModuleFunctor.Inverse.counitApp (R := R) M).hom := sorry

/-- The inverse counit component of the ordinary right-module equivalence is the explicit counit
comparison. -/
@[simp, stacks 09LN "inverse counit component of the ordinary right-module equivalence"]
theorem counitIso_inv_app (M : Bimod.RightModule (algebraMon (R := R) A)) :
    (rightModuleEquivalence (R := R) (A := A)).counitIso.inv.app M =
      (RightModuleFunctor.Inverse.counitApp (R := R) M).inv := sorry

end RightModuleEquivalence

namespace LeftModuleFunctor.Inverse

variable (M : Bimod.LeftModule (algebraMon (R := R) A))

/-- The left action of a categorical left module, read as an ordinary `A`-action. -/
@[stacks 09LN "ordinary action extracted from a categorical left module"]
def smul (a : A) (x : M.X) : M.X :=
  M.actLeft.hom (a ⊗ₜ[R] x)

/-- The scalar-action structure underlying the ordinary module extracted from a categorical
left module. -/
@[implicit_reducible, stacks 09LN "scalar action extracted from a categorical left module"]
def smulStruct : SMul A M.X :=
  ⟨smul (R := R) M⟩

/-- The extracted left action is unital. -/
@[stacks 09LN "unit law for the extracted left action"]
theorem one_smul (x : M.X) : smul (R := R) M 1 x = x := sorry

/-- The extracted left action is associative. -/
@[stacks 09LN "associativity of the extracted left action"]
theorem mul_smul (a b : A) (x : M.X) :
    smul (R := R) M (a * b) x = smul (R := R) M a (smul (R := R) M b x) := sorry

/-- The extracted left action preserves zero in the module variable. -/
@[stacks 09LN "zero law for the extracted left action"]
theorem smul_zero (a : A) : smul (R := R) M a 0 = 0 := sorry

/-- The extracted left action preserves addition in the module variable. -/
@[stacks 09LN "additivity of the extracted left action"]
theorem smul_add (a : A) (x y : M.X) :
    smul (R := R) M a (x + y) = smul (R := R) M a x + smul (R := R) M a y := sorry

/-- The extracted left action is additive in its scalar variable. -/
@[stacks 09LN "scalar additivity of the extracted left action"]
theorem add_smul (a b : A) (x : M.X) :
    smul (R := R) M (a + b) x = smul (R := R) M a x + smul (R := R) M b x := sorry

/-- The zero scalar acts by zero under the extracted left action. -/
@[stacks 09LN "zero scalar law for the extracted left action"]
theorem zero_smul (x : M.X) : smul (R := R) M 0 x = 0 := sorry

/-- The ordinary left `A`-module structure extracted from a categorical left module. -/
@[implicit_reducible, stacks 09LN "ordinary module extracted from a categorical left module"]
def module : Module A M.X where
  smul := (smulStruct (R := R) M).smul
  one_smul := one_smul (R := R) M
  mul_smul := mul_smul (R := R) M
  smul_zero := smul_zero (R := R) M
  smul_add := smul_add (R := R) M
  add_smul := add_smul (R := R) M
  zero_smul := zero_smul (R := R) M

/-- The ordinary module-category object extracted from a categorical left module. -/
@[stacks 09LN "ordinary object extracted from a categorical left module"]
def obj : ModuleCat.{u} A :=
  @ModuleCat.of A _ M.X inferInstance (module (R := R) M)

/-- Scalar multiplication in the extracted ordinary object evaluates the categorical left
action. -/
@[simp, stacks 09LN "scalar action in the extracted ordinary left module"]
theorem obj_smul (a : A) (x : obj (R := R) M) :
    a • x = M.actLeft.hom (a ⊗ₜ[R] x) := sorry

/-- The ground-ring action and the extracted `A`-action form the canonical scalar tower. -/
@[stacks 09LN "scalar tower for an extracted ordinary left module"]
theorem isScalarTower :
    @IsScalarTower R A M.X Algebra.toSMul (smulStruct (R := R) M)
      inferInstance := sorry

/-- Ground scalars commute with the extracted left action. -/
@[stacks 09LN "ground scalar associativity of the extracted left action"]
theorem smul_assoc (r : R) (a : A) (x : M.X) :
    smul (R := R) M (r • a) x = r • smul (R := R) M a x := sorry

/-- Restricting the extracted left action along `algebraMap R A` recovers the original
ground-ring action. -/
@[simp, stacks 09LN "ground scalar action in an extracted ordinary left module"]
theorem algebraMap_smul (r : R) (x : M.X) :
    smul (R := R) M (algebraMap R A r) x = r • x := sorry

variable {M}
variable {N : Bimod.LeftModule (algebraMon (R := R) A)}

/-- The ordinary left-linear map underlying a categorical left-module morphism. -/
@[stacks 09LN "ordinary map extracted from a categorical left-module morphism"]
def linearMap (f : M ⟶ N) :
    @LinearMap A A _ _ (RingHom.id A) M.X N.X inferInstance inferInstance
      (module (R := R) M) (module (R := R) N) :=
  @LinearMap.mk A A _ _ (RingHom.id A) M.X N.X inferInstance inferInstance
    (module (R := R) M) (module (R := R) N) f.hom.hom.toAddHom sorry

/-- The extracted ordinary left-linear map is pointwise the original categorical map. -/
@[simp, stacks 09LN "evaluation of an extracted ordinary left-linear map"]
theorem linearMap_apply (f : M ⟶ N) (x : M.X) :
    linearMap (R := R) f x = f.hom x := sorry

/-- The ordinary module-category morphism underlying a categorical left-module morphism. -/
@[stacks 09LN "ordinary morphism extracted from a categorical left-module morphism"]
def map (f : M ⟶ N) : obj (R := R) M ⟶ obj (R := R) N :=
  @ModuleCat.ofHom A _ M.X N.X inferInstance (module (R := R) M)
    inferInstance (module (R := R) N) (linearMap (R := R) f)

/-- The underlying linear map of an extracted ordinary morphism is `linearMap f`. -/
@[simp, stacks 09LN "underlying map of an extracted ordinary left-module morphism"]
theorem map_hom (f : M ⟶ N) :
    (map (R := R) f).hom = linearMap (R := R) f := sorry

/-- The extracted ordinary module-category morphism is pointwise the original categorical
map. -/
@[simp, stacks 09LN "evaluation of an extracted ordinary left-module morphism"]
theorem map_apply (f : M ⟶ N) (x : M.X) :
    map (R := R) f x = f.hom x := sorry

/-- Extracting ordinary left modules from categorical left modules defines a functor. -/
@[stacks 09LN "ordinary left-module extraction functor"]
def functor : Bimod.LeftModule (algebraMon (R := R) A) ⥤ ModuleCat.{u} A where
  obj := obj (R := R)
  map := map (R := R)
  map_id := sorry
  map_comp := sorry

/-- The extraction functor returns the explicitly extracted ordinary object. -/
@[simp, stacks 09LN "ordinary left-module extraction on objects"]
theorem functor_obj (M : Bimod.LeftModule (algebraMon (R := R) A)) :
    (functor (R := R) (A := A)).obj M = obj (R := R) M := sorry

/-- The extraction functor maps a categorical morphism by its extracted ordinary map. -/
@[simp, stacks 09LN "ordinary left-module extraction on morphisms"]
theorem functor_map {M N : Bimod.LeftModule (algebraMon (R := R) A)} (f : M ⟶ N) :
    (functor (R := R) (A := A)).map f = map (R := R) f := sorry

variable (P : ModuleCat.{u} A)

/-- The objectwise unit identifying an ordinary left module with realization followed by
extraction. -/
@[stacks 09LN "unit of ordinary left-module realization and extraction"]
def unitApp : P ≅ obj (R := R) ((leftModuleFunctor (R := R) (A := A)).obj P) where
  hom := @ModuleCat.ofHom A _ P
    ((leftModuleFunctor (R := R) (A := A)).obj P).X inferInstance inferInstance
    inferInstance (module (R := R) ((leftModuleFunctor (R := R) (A := A)).obj P))
    (@LinearMap.mk A A _ _ (RingHom.id A) P
      ((leftModuleFunctor (R := R) (A := A)).obj P).X inferInstance inferInstance
      inferInstance (module (R := R) ((leftModuleFunctor (R := R) (A := A)).obj P))
      (𝟙 P : P ⟶ P).hom.toAddHom sorry)
  inv := @ModuleCat.ofHom A _
    ((leftModuleFunctor (R := R) (A := A)).obj P).X P inferInstance
    (module (R := R) ((leftModuleFunctor (R := R) (A := A)).obj P))
    inferInstance inferInstance
    (@LinearMap.mk A A _ _ (RingHom.id A)
      ((leftModuleFunctor (R := R) (A := A)).obj P).X P inferInstance inferInstance
      (module (R := R) ((leftModuleFunctor (R := R) (A := A)).obj P))
      inferInstance (𝟙 P : P ⟶ P).hom.toAddHom sorry)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward unit comparison is the identity on elements. -/
@[simp, stacks 09LN "forward unit of ordinary left-module realization on elements"]
theorem unitApp_hom_apply (x : P) : (unitApp (R := R) P).hom x = x := sorry

/-- The inverse unit comparison is the identity on elements. -/
@[simp, stacks 09LN "inverse unit of ordinary left-module realization on elements"]
theorem unitApp_inv_apply
    (x : obj (R := R) ((leftModuleFunctor (R := R) (A := A)).obj P)) :
    (unitApp (R := R) P).inv x = x := sorry

/-- The objectwise unit comparison is natural in the ordinary left module. -/
@[reassoc, stacks 09LN "naturality of the ordinary left-module realization unit"]
theorem unitApp_naturality {P Q : ModuleCat.{u} A} (f : P ⟶ Q) :
    f ≫ (unitApp (R := R) Q).hom =
      (unitApp (R := R) P).hom ≫
        (leftModuleFunctor (R := R) (A := A) ⋙ functor (R := R) (A := A)).map f := sorry

/-- The unit natural isomorphism for ordinary left-module realization and extraction. -/
@[stacks 09LN "unit isomorphism for ordinary left-module realization"]
def unitIso :
    𝟭 (ModuleCat.{u} A) ≅
      leftModuleFunctor (R := R) (A := A) ⋙ functor (R := R) (A := A) :=
  NatIso.ofComponents (unitApp (R := R)) (fun f ↦ unitApp_naturality (R := R) f)

variable (M)

/-- The underlying ground-ring comparison for extraction followed by realization. -/
@[stacks 09LN "underlying counit of ordinary left-module realization"]
def counitUnderlyingIso :
    (ModuleCat.restrictScalars (algebraMap R A)).obj (obj (R := R) M) ≅ M.X :=
  @ModuleCat.RestrictScalars.identityIso R A _ _ _ M.X inferInstance inferInstance
    (module (R := R) M) (isScalarTower (R := R) M)

/-- The objectwise counit identifying extraction followed by realization with the original
categorical left module. -/
@[stacks 09LN "counit of ordinary left-module realization and extraction"]
def counitApp :
    (leftModuleFunctor (R := R) (A := A)).obj (obj (R := R) M) ≅ M :=
  Bimod.isoOfIso (counitUnderlyingIso (R := R) M) sorry sorry

/-- The forward counit comparison is the identity on elements. -/
@[simp, stacks 09LN "forward counit of ordinary left-module realization on elements"]
theorem counitApp_hom_apply
    (x : ((leftModuleFunctor (R := R) (A := A)).obj (obj (R := R) M)).X) :
    (counitApp (R := R) M).hom.hom x = x := sorry

/-- The inverse counit comparison is the identity on elements. -/
@[simp, stacks 09LN "inverse counit of ordinary left-module realization on elements"]
theorem counitApp_inv_apply (x : M.X) :
    (counitApp (R := R) M).inv.hom x = x := sorry

/-- The objectwise counit comparison is natural in the categorical left module. -/
@[reassoc, stacks 09LN "naturality of the ordinary left-module realization counit"]
theorem counitApp_naturality
    {M N : Bimod.LeftModule (algebraMon (R := R) A)} (f : M ⟶ N) :
    (functor (R := R) (A := A) ⋙ leftModuleFunctor (R := R) (A := A)).map f ≫
        (counitApp (R := R) N).hom =
      (counitApp (R := R) M).hom ≫ f := sorry

/-- The counit natural isomorphism for ordinary left-module extraction and realization. -/
@[stacks 09LN "counit isomorphism for ordinary left-module realization"]
def counitIso :
    functor (R := R) (A := A) ⋙ leftModuleFunctor (R := R) (A := A) ≅
      𝟭 (Bimod.LeftModule (algebraMon (R := R) A)) :=
  NatIso.ofComponents (counitApp (R := R)) (fun f ↦ counitApp_naturality (R := R) f)

/-- The unit and counit comparisons satisfy the realization-side triangle identity. -/
@[stacks 09LN "triangle identity for ordinary left-module realization"]
theorem equivalence_triangle (P : ModuleCat.{u} A) :
    (leftModuleFunctor (R := R) (A := A)).map ((unitIso (R := R) (A := A)).hom.app P) ≫
        (counitIso (R := R) (A := A)).hom.app
          ((leftModuleFunctor (R := R) (A := A)).obj P) =
      𝟙 ((leftModuleFunctor (R := R) (A := A)).obj P) := sorry

end LeftModuleFunctor.Inverse

/-- Ordinary left `A`-modules and categorical left modules over `algebraMon A` are canonically
equivalent. -/
@[stacks 09LN "ordinary and categorical left modules are equivalent"]
def leftModuleEquivalence :
    ModuleCat.{u} A ≌ Bimod.LeftModule (algebraMon (R := R) A) :=
  CategoryTheory.Equivalence.mk'
    (leftModuleFunctor (R := R) (A := A))
    (LeftModuleFunctor.Inverse.functor (R := R) (A := A))
    (LeftModuleFunctor.Inverse.unitIso (R := R) (A := A))
    (LeftModuleFunctor.Inverse.counitIso (R := R) (A := A))
    (LeftModuleFunctor.Inverse.equivalence_triangle (R := R) (A := A))

/-- The forward functor of `leftModuleEquivalence` is ordinary realization. -/
@[simp, stacks 09LN "forward functor of the ordinary left-module equivalence"]
theorem leftModuleEquivalence_functor :
    (leftModuleEquivalence (R := R) (A := A)).functor =
      leftModuleFunctor (R := R) (A := A) := sorry

/-- The inverse functor of `leftModuleEquivalence` extracts the ordinary module action. -/
@[simp, stacks 09LN "inverse functor of the ordinary left-module equivalence"]
theorem leftModuleEquivalence_inverse :
    (leftModuleEquivalence (R := R) (A := A)).inverse =
      LeftModuleFunctor.Inverse.functor (R := R) (A := A) := sorry

namespace LeftModuleFunctor.Inverse

/-- The ordinary left-module extraction functor is fully faithful. -/
@[stacks 09LN "ordinary left-module extraction is fully faithful"]
noncomputable def fullyFaithful :
    (functor (R := R) (A := A)).FullyFaithful :=
  (leftModuleEquivalence (R := R) (A := A)).fullyFaithfulInverse

/-- Typeclass search recognizes ordinary left-module extraction as full. -/
@[stacks 09LN "ordinary left-module extraction is full"]
instance functorFull : (functor (R := R) (A := A)).Full := sorry

/-- Typeclass search recognizes ordinary left-module extraction as faithful. -/
@[stacks 09LN "ordinary left-module extraction is faithful"]
instance functorFaithful : (functor (R := R) (A := A)).Faithful := sorry

end LeftModuleFunctor.Inverse

namespace LeftModuleEquivalence

/-- The forward unit component of the ordinary left-module equivalence is the explicit unit
comparison. -/
@[simp, stacks 09LN "forward unit component of the ordinary left-module equivalence"]
theorem unitIso_hom_app (P : ModuleCat.{u} A) :
    (leftModuleEquivalence (R := R) (A := A)).unitIso.hom.app P =
      (LeftModuleFunctor.Inverse.unitApp (R := R) P).hom := sorry

/-- The inverse unit component of the ordinary left-module equivalence is the explicit unit
comparison. -/
@[simp, stacks 09LN "inverse unit component of the ordinary left-module equivalence"]
theorem unitIso_inv_app (P : ModuleCat.{u} A) :
    (leftModuleEquivalence (R := R) (A := A)).unitIso.inv.app P =
      (LeftModuleFunctor.Inverse.unitApp (R := R) P).inv := sorry

/-- The forward counit component of the ordinary left-module equivalence is the explicit counit
comparison. -/
@[simp, stacks 09LN "forward counit component of the ordinary left-module equivalence"]
theorem counitIso_hom_app (M : Bimod.LeftModule (algebraMon (R := R) A)) :
    (leftModuleEquivalence (R := R) (A := A)).counitIso.hom.app M =
      (LeftModuleFunctor.Inverse.counitApp (R := R) M).hom := sorry

/-- The inverse counit component of the ordinary left-module equivalence is the explicit counit
comparison. -/
@[simp, stacks 09LN "inverse counit component of the ordinary left-module equivalence"]
theorem counitIso_inv_app (M : Bimod.LeftModule (algebraMon (R := R) A)) :
    (leftModuleEquivalence (R := R) (A := A)).counitIso.inv.app M =
      (LeftModuleFunctor.Inverse.counitApp (R := R) M).inv := sorry

end LeftModuleEquivalence

#synth (RightModuleFunctor.Inverse.functor (R := R) (A := A)).Full
#synth (RightModuleFunctor.Inverse.functor (R := R) (A := A)).Faithful
#synth (LeftModuleFunctor.Inverse.functor (R := R) (A := A)).Full
#synth (LeftModuleFunctor.Inverse.functor (R := R) (A := A)).Faithful

end Module.Bimodule
