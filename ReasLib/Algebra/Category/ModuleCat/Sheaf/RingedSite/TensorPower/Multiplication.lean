/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication of tensor powers on a ringed site

The left-recursive tensor powers carry canonical concatenation isomorphisms.  This leaf owns
those isomorphisms, their multiplication morphisms, and the degree-zero unit without passing
through geometric specializations.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.TensorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (𝒪 : Sheaf J CommRingCat.{w})

/-- The canonical concatenation isomorphism between the degree-`n` and degree-`m` tensor powers. -/
@[stacks 01CF "multiplication of tensor powers"]
noncomputable abbrev addIso
    (F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) :
    (n m : ℕ) → tensorObj (sheaf 𝒪 F n) (sheaf 𝒪 F m) ≅ sheaf 𝒪 F (n + m) :=
  tensorPowerWithDegreeZeroAddIso
    (unitIsoTensorUnit (J := J) (𝒪 := 𝒪)) F

/-- The multiplication morphism between the degree-`n` and degree-`m` tensor powers. -/
@[stacks 01CF "tensor-power multiplication morphism"]
noncomputable def mul
    (F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) (n m : ℕ) :
    tensorObj (sheaf 𝒪 F n) (sheaf 𝒪 F m) ⟶ sheaf 𝒪 F (n + m) :=
  (addIso 𝒪 F n m).hom

/-- The degree-zero unit morphism of the tensor-power grading. -/
@[stacks 01CF "degree-zero unit of tensor powers"]
noncomputable def one
    (F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) :
    unitModule J 𝒪 ⟶ sheaf 𝒪 F 0 :=
  𝟙 (unitModule J 𝒪)

/-- Tensor-power multiplication is natural in the module sheaf. -/
@[stacks 01CF "naturality of tensor-power multiplication"]
theorem mul_naturality
    {F G : ringedSiteModuleCategory.{u, v, w, w} J 𝒪} (f : F ⟶ G) (n m : ℕ) :
    tensorHom (map 𝒪 f n) (map 𝒪 f m) ≫ mul 𝒪 G n m =
      mul 𝒪 F n m ≫ map 𝒪 f (n + m) := sorry

/-- The degree-zero tensor-power unit is natural in the module sheaf. -/
@[stacks 01CF "naturality of the tensor-power unit"]
theorem one_naturality
    {F G : ringedSiteModuleCategory.{u, v, w, w} J 𝒪} (f : F ⟶ G) :
    one 𝒪 F ≫ map 𝒪 f 0 = one 𝒪 G := sorry

/-- Tensor-power multiplication is associative, with the degree transport displayed. -/
@[stacks 01CF "associativity of tensor-power multiplication"]
theorem mul_assoc
    (F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) (n m k : ℕ) :
    (α_ (sheaf 𝒪 F n) (sheaf 𝒪 F m) (sheaf 𝒪 F k)).hom ≫
        (sheaf 𝒪 F n ◁ mul 𝒪 F m k) ≫ mul 𝒪 F n (m + k) =
      (mul 𝒪 F n m ▷ sheaf 𝒪 F k) ≫ mul 𝒪 F (n + m) k ≫
        eqToHom (congrArg (sheaf 𝒪 F) (Nat.add_assoc n m k)) := sorry

/-- The degree-zero tensor power is a left unit for tensor-power multiplication. -/
@[stacks 01CF "left unit law for tensor-power multiplication"]
theorem one_mul
    (F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) (n : ℕ) :
    (λ_ (sheaf 𝒪 F n)).hom =
      ((unitIsoTensorUnit (J := J) (𝒪 := 𝒪)).inv ▷ sheaf 𝒪 F n) ≫
        (one 𝒪 F ▷ sheaf 𝒪 F n) ≫ mul 𝒪 F 0 n ≫
          eqToHom (congrArg (sheaf 𝒪 F) (Nat.zero_add n)) := sorry

/-- The degree-zero tensor power is a right unit for tensor-power multiplication. -/
@[stacks 01CF "right unit law for tensor-power multiplication"]
theorem mul_one
    (F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) (n : ℕ) :
    (ρ_ (sheaf 𝒪 F n)).hom =
      (sheaf 𝒪 F n ◁ (unitIsoTensorUnit (J := J) (𝒪 := 𝒪)).inv) ≫
        (sheaf 𝒪 F n ◁ one 𝒪 F) ≫ mul 𝒪 F n 0 ≫
          eqToHom (congrArg (sheaf 𝒪 F) (Nat.add_zero n)) := sorry

end SheafOfModules.RingedSite.TensorPower


