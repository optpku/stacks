module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationMonoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication of exterior-power sheaves

This leaf transports fixed-degree exterior multiplication through the canonical monoidal module
sheafification comparison.  It provides the multiplication maps underlying the exterior graded
algebra on every commutative ringed site.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.ExteriorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/-- The multiplication morphism
`Λ^n(F) ⊗ Λ^m(F) ⟶ Λ^(n + m)(F)` on a commutative ringed site. -/
@[stacks 01CF "multiplication of exterior-power sheaves"]
noncomputable def mul
    (F : ringedSiteModuleCategory J 𝒪) (n m : ℕ) :
    tensorObj (sheaf 𝒪 F n) (sheaf 𝒪 F m) ⟶ sheaf 𝒪 F (n + m) :=
  (ModuleSheafification.tensorIso 𝒪 (presheaf 𝒪 F n) (presheaf 𝒪 F m)).hom ≫
    (moduleSheafification 𝒪).map
      (PresheafOfModules.ExteriorPower.mulHom 𝒪.obj F.val n m)

/-- Exterior-power sheaf multiplication is natural in the module sheaf. -/
theorem mul_naturality
    {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) (n m : ℕ) :
    tensorHom (map 𝒪 f n) (map 𝒪 f m) ≫ mul 𝒪 G n m =
      mul 𝒪 F n m ≫ map 𝒪 f (n + m) := sorry

/-- The degree-zero unit morphism from the structure module to `Λ⁰(F)` on a
commutative ringed site. -/
@[stacks 01CF "degree-zero unit of exterior-power sheaves"]
noncomputable def one (F : ringedSiteModuleCategory J 𝒪) :
    unitModule J 𝒪 ⟶ sheaf 𝒪 F 0 :=
  (moduleSheafificationValIso 𝒪 (unitModule J 𝒪)).inv ≫
    (moduleSheafification 𝒪).map
      (PresheafOfModules.ExteriorPower.oneHom 𝒪.obj F.val)

/-- The degree-zero unit is the sheafification of the sectionwise empty exterior product. -/
theorem one_eq_sheafification (F : ringedSiteModuleCategory J 𝒪) :
    one 𝒪 F =
      (moduleSheafificationValIso 𝒪 (unitModule J 𝒪)).inv ≫
        (moduleSheafification 𝒪).map
          (PresheafOfModules.ExteriorPower.oneHom 𝒪.obj F.val) := sorry

/-- The degree-zero unit is natural in the module sheaf. -/
theorem one_naturality
    {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) :
    one 𝒪 F ≫ map 𝒪 f 0 = one 𝒪 G := sorry

/-- Exterior-power sheaf multiplication is associative, with degree reindexing explicit. -/
theorem mul_assoc
    (F : ringedSiteModuleCategory J 𝒪) (n m k : ℕ) :
    (α_ (sheaf 𝒪 F n) (sheaf 𝒪 F m) (sheaf 𝒪 F k)).hom ≫
        (sheaf 𝒪 F n ◁ mul 𝒪 F m k) ≫ mul 𝒪 F n (m + k) =
      (mul 𝒪 F n m ▷ sheaf 𝒪 F k) ≫ mul 𝒪 F (n + m) k ≫
        eqToHom (congrArg (sheaf 𝒪 F) (Nat.add_assoc n m k)) := sorry

/-- The degree-zero exterior-power sheaf is a left unit. -/
theorem one_mul
    (F : ringedSiteModuleCategory J 𝒪) (n : ℕ) :
    (λ_ (sheaf 𝒪 F n)).hom =
      ((unitIsoTensorUnit (J := J) (𝒪 := 𝒪)).inv ▷ sheaf 𝒪 F n) ≫
        (one 𝒪 F ▷ sheaf 𝒪 F n) ≫ mul 𝒪 F 0 n ≫
          eqToHom (congrArg (sheaf 𝒪 F) (Nat.zero_add n)) := sorry

/-- The degree-zero exterior-power sheaf is a right unit. -/
theorem mul_one
    (F : ringedSiteModuleCategory J 𝒪) (n : ℕ) :
    (ρ_ (sheaf 𝒪 F n)).hom =
      (sheaf 𝒪 F n ◁ (unitIsoTensorUnit (J := J) (𝒪 := 𝒪)).inv) ≫
        (sheaf 𝒪 F n ◁ one 𝒪 F) ≫ mul 𝒪 F n 0 ≫
          eqToHom (congrArg (sheaf 𝒪 F) (Nat.add_zero n)) := sorry

end SheafOfModules.RingedSite.ExteriorPower

