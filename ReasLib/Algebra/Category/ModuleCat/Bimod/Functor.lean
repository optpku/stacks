/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Bimod
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Restrict
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ordinary module categories as categorical module objects

This file promotes the concrete one-sided module bridge to functors from the ordinary module
categories.  Objects first acquire their canonical ground-ring action by restriction of scalars;
the target remains Mathlib's category of module objects over `algebraMon A`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace Module.Bimodule

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]

namespace RightModuleFunctor

/-- The ground-ring module obtained from an ordinary right `A`-module by restricting its
`Aᵐᵒᵖ`-action along `R → Aᵐᵒᵖ`. -/
@[stacks 09LN "restricted carrier of an ordinary right module"]
abbrev restricted (M : ModuleCat.{u} Aᵐᵒᵖ) : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars (algebraMap R Aᵐᵒᵖ)).obj M

/-- The categorical right-module morphism induced by an ordinary right-linear map. -/
@[stacks 09LN "ordinary right-module realization on morphisms"]
def map {M N : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ N) :
    toRightModule (R := R) (A := A) (restricted (R := R) M) ⟶
      toRightModule (R := R) (A := A) (restricted (R := R) N) :=
  ToRightModule.map (R := R) (N := restricted (R := R) M)
    (N' := restricted (R := R) N) f.hom

/-- The ordinary right-linear map recovered from a morphism between realized right modules. -/
@[stacks 09LN "ordinary right-module realization inverse on linear maps"]
def linearPreimage {M N : ModuleCat.{u} Aᵐᵒᵖ}
    (f : toRightModule (R := R) (A := A) (restricted (R := R) M) ⟶
      toRightModule (R := R) (A := A) (restricted (R := R) N)) :
    restricted (R := R) M →ₗ[Aᵐᵒᵖ] restricted (R := R) N :=
  ToRightModule.ofHom (N := restricted (R := R) M)
    (N' := restricted (R := R) N) f

/-- The ordinary module-category morphism recovered from a morphism between realized right
modules. -/
@[stacks 09LN "ordinary right-module realization inverse on morphisms"]
def preimage {M N : ModuleCat.{u} Aᵐᵒᵖ}
    (f : toRightModule (R := R) (A := A) (restricted (R := R) M) ⟶
      toRightModule (R := R) (A := A) (restricted (R := R) N)) : M ⟶ N :=
  ModuleCat.ofHom (linearPreimage (R := R) f)

end RightModuleFunctor

/-- Ordinary right `A`-modules, modeled as left modules over `Aᵐᵒᵖ`, form categorical right
modules over `algebraMon A`. -/
@[stacks 09LN "ordinary right-module realization functor"]
noncomputable def rightModuleFunctor :
    ModuleCat.{u} Aᵐᵒᵖ ⥤
      CategoryTheory.Bimod.RightModule (algebraMon (R := R) A) where
  obj M :=
    toRightModule (R := R) (A := A) (RightModuleFunctor.restricted (R := R) M)
  map f := RightModuleFunctor.map (R := R) f
  map_id := sorry
  map_comp := sorry

/-- On objects, `rightModuleFunctor` restricts scalars to `R` and applies `toRightModule`. -/
@[simp, stacks 09LN "ordinary right-module realization on objects"]
theorem rightModuleFunctor_obj (M : ModuleCat.{u} Aᵐᵒᵖ) :
    (rightModuleFunctor (R := R) (A := A)).obj M =
      toRightModule (R := R) (A := A)
        (RightModuleFunctor.restricted (R := R) M) := sorry

/-- On morphisms, `rightModuleFunctor` is the categorical form of the underlying right-linear
map. -/
@[simp, stacks 09LN "ordinary right-module realization on morphisms"]
theorem rightModuleFunctor_map {M N : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ N) :
    (rightModuleFunctor (R := R) (A := A)).map f =
      RightModuleFunctor.map (R := R) f := sorry

namespace RightModuleFunctor

/-- The right-module realization of an ordinary morphism has the same pointwise action. -/
@[simp, stacks 09LN "ordinary right-module realization on elements"]
theorem map_apply {M N : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ N) (m : M) :
    (map (R := R) f).hom m = f.hom m := sorry

/-- Recovering the right-linear map of a categorical morphism preserves evaluation. -/
@[simp, stacks 09LN "ordinary right-module realization inverse on elements"]
theorem linearPreimage_apply {M N : ModuleCat.{u} Aᵐᵒᵖ}
    (f : (rightModuleFunctor (R := R) (A := A)).obj M ⟶
      (rightModuleFunctor (R := R) (A := A)).obj N) (m : M) :
    linearPreimage (R := R) f m = f.hom m := sorry

/-- The underlying right-linear map of `preimage f` is `linearPreimage f`. -/
@[simp, stacks 09LN "underlying map of the ordinary right-module realization inverse"]
theorem preimage_hom {M N : ModuleCat.{u} Aᵐᵒᵖ}
    (f : (rightModuleFunctor (R := R) (A := A)).obj M ⟶
      (rightModuleFunctor (R := R) (A := A)).obj N) :
    (preimage (R := R) f).hom = linearPreimage (R := R) f := sorry

/-- Recovering an ordinary right-module morphism preserves its pointwise action. -/
@[simp, stacks 09LN "ordinary right-module realization preimage on elements"]
theorem preimage_apply {M N : ModuleCat.{u} Aᵐᵒᵖ}
    (f : (rightModuleFunctor (R := R) (A := A)).obj M ⟶
      (rightModuleFunctor (R := R) (A := A)).obj N) (m : M) :
    (preimage (R := R) f).hom m = f.hom m := sorry

/-- Realizing and then recovering an ordinary right-module morphism is the identity. -/
@[simp, stacks 09LN "inverse after ordinary right-module realization"]
theorem preimage_map {M N : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ N) :
    preimage (R := R) (map (R := R) f) = f := sorry

/-- Recovering and then realizing a categorical right-module morphism is the identity. -/
@[simp, stacks 09LN "ordinary right-module realization after inverse"]
theorem map_preimage {M N : ModuleCat.{u} Aᵐᵒᵖ}
    (f : (rightModuleFunctor (R := R) (A := A)).obj M ⟶
      (rightModuleFunctor (R := R) (A := A)).obj N) :
    map (R := R) (preimage (R := R) f) = f := sorry

/-- The realization functor from ordinary right modules to categorical right modules is fully
faithful. -/
@[stacks 09LN "ordinary right-module realization is fully faithful"]
noncomputable def fullyFaithful :
    (rightModuleFunctor (R := R) (A := A)).FullyFaithful where
  preimage f := RightModuleFunctor.preimage (R := R) f
  map_preimage := sorry
  preimage_map := sorry

/-- Typeclass search uses the bundled fully faithful structure to recognize the right-module
realization functor as full. -/
@[stacks 09LN "ordinary right-module realization is full"]
instance functorFull :
    (rightModuleFunctor (R := R) (A := A)).Full := sorry

/-- Typeclass search uses the bundled fully faithful structure to recognize the right-module
realization functor as faithful. -/
@[stacks 09LN "ordinary right-module realization is faithful"]
instance functorFaithful :
    (rightModuleFunctor (R := R) (A := A)).Faithful := sorry

end RightModuleFunctor

namespace LeftModuleFunctor

/-- The ground-ring module obtained from an ordinary left `A`-module by restricting scalars along
`R → A`. -/
@[stacks 09LN "restricted carrier of an ordinary left module"]
abbrev restricted (M : ModuleCat.{u} A) : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars (algebraMap R A)).obj M

/-- The categorical left-module morphism induced by an ordinary left-linear map. -/
@[stacks 09LN "ordinary left-module realization on morphisms"]
def map {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    toLeftModule (R := R) (A := A) (restricted (R := R) M) ⟶
      toLeftModule (R := R) (A := A) (restricted (R := R) N) :=
  ToLeftModule.map (R := R) (N := restricted (R := R) M)
    (N' := restricted (R := R) N) f.hom

/-- The ordinary left-linear map recovered from a morphism between realized left modules. -/
@[stacks 09LN "ordinary left-module realization inverse on linear maps"]
def linearPreimage {M N : ModuleCat.{u} A}
    (f : toLeftModule (R := R) (A := A) (restricted (R := R) M) ⟶
      toLeftModule (R := R) (A := A) (restricted (R := R) N)) :
    restricted (R := R) M →ₗ[A] restricted (R := R) N :=
  ToLeftModule.ofHom (N := restricted (R := R) M)
    (N' := restricted (R := R) N) f

/-- The ordinary module-category morphism recovered from a morphism between realized left
modules. -/
@[stacks 09LN "ordinary left-module realization inverse on morphisms"]
def preimage {M N : ModuleCat.{u} A}
    (f : toLeftModule (R := R) (A := A) (restricted (R := R) M) ⟶
      toLeftModule (R := R) (A := A) (restricted (R := R) N)) : M ⟶ N :=
  ModuleCat.ofHom (linearPreimage (R := R) f)

end LeftModuleFunctor

/-- Ordinary left `A`-modules form categorical left modules over `algebraMon A`. -/
@[stacks 09LN "ordinary left-module realization functor"]
noncomputable def leftModuleFunctor :
    ModuleCat.{u} A ⥤ CategoryTheory.Bimod.LeftModule (algebraMon (R := R) A) where
  obj M :=
    toLeftModule (R := R) (A := A) (LeftModuleFunctor.restricted (R := R) M)
  map f := LeftModuleFunctor.map (R := R) f
  map_id := sorry
  map_comp := sorry

/-- On objects, `leftModuleFunctor` restricts scalars to `R` and applies `toLeftModule`. -/
@[simp, stacks 09LN "ordinary left-module realization on objects"]
theorem leftModuleFunctor_obj (M : ModuleCat.{u} A) :
    (leftModuleFunctor (R := R) (A := A)).obj M =
      toLeftModule (R := R) (A := A)
        (LeftModuleFunctor.restricted (R := R) M) := sorry

/-- On morphisms, `leftModuleFunctor` is the categorical form of the underlying left-linear
map. -/
@[simp, stacks 09LN "ordinary left-module realization on morphisms"]
theorem leftModuleFunctor_map {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (leftModuleFunctor (R := R) (A := A)).map f =
      LeftModuleFunctor.map (R := R) f := sorry

namespace LeftModuleFunctor

/-- The left-module realization of an ordinary morphism has the same pointwise action. -/
@[simp, stacks 09LN "ordinary left-module realization on elements"]
theorem map_apply {M N : ModuleCat.{u} A} (f : M ⟶ N) (m : M) :
    (map (R := R) f).hom m = f.hom m := sorry

/-- Recovering the left-linear map of a categorical morphism preserves evaluation. -/
@[simp, stacks 09LN "ordinary left-module realization inverse on elements"]
theorem linearPreimage_apply {M N : ModuleCat.{u} A}
    (f : (leftModuleFunctor (R := R) (A := A)).obj M ⟶
      (leftModuleFunctor (R := R) (A := A)).obj N) (m : M) :
    linearPreimage (R := R) f m = f.hom m := sorry

/-- The underlying left-linear map of `preimage f` is `linearPreimage f`. -/
@[simp, stacks 09LN "underlying map of the ordinary left-module realization inverse"]
theorem preimage_hom {M N : ModuleCat.{u} A}
    (f : (leftModuleFunctor (R := R) (A := A)).obj M ⟶
      (leftModuleFunctor (R := R) (A := A)).obj N) :
    (preimage (R := R) f).hom = linearPreimage (R := R) f := sorry

/-- Recovering an ordinary left-module morphism preserves its pointwise action. -/
@[simp, stacks 09LN "ordinary left-module realization preimage on elements"]
theorem preimage_apply {M N : ModuleCat.{u} A}
    (f : (leftModuleFunctor (R := R) (A := A)).obj M ⟶
      (leftModuleFunctor (R := R) (A := A)).obj N) (m : M) :
    (preimage (R := R) f).hom m = f.hom m := sorry

/-- Realizing and then recovering an ordinary left-module morphism is the identity. -/
@[simp, stacks 09LN "inverse after ordinary left-module realization"]
theorem preimage_map {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    preimage (R := R) (map (R := R) f) = f := sorry

/-- Recovering and then realizing a categorical left-module morphism is the identity. -/
@[simp, stacks 09LN "ordinary left-module realization after inverse"]
theorem map_preimage {M N : ModuleCat.{u} A}
    (f : (leftModuleFunctor (R := R) (A := A)).obj M ⟶
      (leftModuleFunctor (R := R) (A := A)).obj N) :
    map (R := R) (preimage (R := R) f) = f := sorry

/-- The realization functor from ordinary left modules to categorical left modules is fully
faithful. -/
@[stacks 09LN "ordinary left-module realization is fully faithful"]
noncomputable def fullyFaithful :
    (leftModuleFunctor (R := R) (A := A)).FullyFaithful where
  preimage f := LeftModuleFunctor.preimage (R := R) f
  map_preimage := sorry
  preimage_map := sorry

/-- Typeclass search uses the bundled fully faithful structure to recognize the left-module
realization functor as full. -/
@[stacks 09LN "ordinary left-module realization is full"]
instance functorFull :
    (leftModuleFunctor (R := R) (A := A)).Full := sorry

/-- Typeclass search uses the bundled fully faithful structure to recognize the left-module
realization functor as faithful. -/
@[stacks 09LN "ordinary left-module realization is faithful"]
instance functorFaithful :
    (leftModuleFunctor (R := R) (A := A)).Faithful := sorry

end LeftModuleFunctor

#synth (rightModuleFunctor (R := R) (A := A)).Full
#synth (rightModuleFunctor (R := R) (A := A)).Faithful
#synth (leftModuleFunctor (R := R) (A := A)).Full
#synth (leftModuleFunctor (R := R) (A := A)).Faithful

end Module.Bimodule
