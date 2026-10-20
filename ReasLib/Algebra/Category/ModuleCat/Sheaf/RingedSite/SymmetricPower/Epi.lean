module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricPower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Epimorphisms and symmetric powers on ringed sites

This is the topology-independent sheaf-level owner for preservation of quotients by symmetric
powers.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.SymmetricPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/-- Symmetric-power sheafification preserves epimorphisms on a commutative ringed site. -/
@[stacks 01CJ "symmetric powers preserve epimorphisms on a ringed site", instance]
instance preservesEpimorphisms (n : ℕ) :
    (functor 𝒪 n).PreservesEpimorphisms := sorry

/-- An epimorphism of module sheaves induces an epimorphism on every symmetric power. -/
@[stacks 01CJ "epimorphism on a symmetric-power sheaf"]
theorem map_epi {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) (n : ℕ) [Epi f] :
    Epi (map 𝒪 f n) := sorry

end SheafOfModules.RingedSite.SymmetricPower
