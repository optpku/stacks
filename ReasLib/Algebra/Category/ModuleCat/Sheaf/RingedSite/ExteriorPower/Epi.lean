/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Multiplication
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Epimorphisms and exterior powers on ringed sites

This leaf owns preservation of quotient maps by exterior-power sheaves before specializing to
ringed spaces.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.ExteriorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/-- Exterior-power sheafification preserves epimorphisms on a commutative ringed site. -/
@[stacks 01CJ "exterior powers preserve epimorphisms on a ringed site", instance]
instance preservesEpimorphisms (n : ℕ) :
    (functor 𝒪 n).PreservesEpimorphisms := sorry

/-- An epimorphism of module sheaves induces an epimorphism on every exterior power. -/
@[stacks 01CJ "epimorphism on an exterior-power sheaf"]
theorem map_epi {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) (n : ℕ) [Epi f] :
    Epi (map 𝒪 f n) := sorry

/-- Left multiplication by degree one generates the next exterior-power sheaf. -/
@[stacks 062K "left degree-one generation of exterior powers", instance]
instance degreeOne_mul_epi (F : ringedSiteModuleCategory J 𝒪) (n : ℕ) :
    Epi (mul 𝒪 F 1 (n + 1)) := sorry

/-- Right multiplication by degree one generates the next exterior-power sheaf. -/
@[stacks 062K "right degree-one generation of exterior powers", instance]
instance mul_degreeOne_epi (F : ringedSiteModuleCategory J 𝒪) (n : ℕ) :
    Epi (mul 𝒪 F (n + 1) 1) := sorry

end SheafOfModules.RingedSite.ExteriorPower

