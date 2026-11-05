module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Algebra

@[expose] public section

open CategoryTheory

universe u v

namespace SheafOfModules.RingedSite.GradedAlgebraSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{max u v}]
variable [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {ι : Type} [AddMonoid ι]

/-- A graded algebra sheaf is quasi-coherent when each of its degreewise module sheaves is
quasi-coherent. -/
abbrev IsQuasicoherent (𝒜 : GradedAlgebraSheaf 𝒪 ι) : Prop :=
  ∀ n : ι, (𝒜.obj n).IsQuasicoherent

end SheafOfModules.RingedSite.GradedAlgebraSheaf
