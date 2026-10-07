module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Module.FiniteType
public import stacks_project.Chap30.Lemma_30_20_2_HigherDirectImage
public import stacks_project.Chap30.Lemma_30_20_2_Rees

/-!
# Lemma 30.20.2

For a proper morphism `f : X ⟶ Y` with `Y` locally Noetherian, a quasi-coherent
ideal sheaf `I ⊂ 𝒪_Y`, and a coherent `𝒪_X`-module `F`, the graded module sheaf
`M = ⨁_{n ≥ 0} R^p f_*(I^n F)` over the Rees algebra `A = ⨁_{n ≥ 0} I^n` is
quasi-coherent and of finite type.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite.GradedModuleSheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace IdealPowerCohomology

variable {Y : Scheme.{u}} (I : Y.IdealSheafData) [I.toModule.IsQuasicoherent]
variable {X : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p : ℕ)

/-- Lemma 30.20.2 (1): given a morphism of schemes `f : X ⟶ Y`, a quasi-coherent
sheaf `F` on `X`, and a quasi-coherent sheaf of ideals `I ⊂ 𝒪_Y`, if `Y` is
locally Noetherian, `f` is proper, and `F` is coherent, then
`M = ⨁_{n ≥ 0} R^p f_*(I^n F)` is a quasi-coherent graded module over
`A = ⨁_{n ≥ 0} I^n`. -/
@[stacks 02O9]
instance isQuasicoherent [IsLocallyNoetherian Y] [IsProper f] [F.IsCoherent]
    (n : ℤ) : (gradedModule I f F p n).IsQuasicoherent :=
  sorry

/-- Lemma 30.20.2 (2): under the same hypotheses, `M = ⨁_{n ≥ 0} R^p f_*(I^n F)`
is of finite type as a graded module over `A = ⨁_{n ≥ 0} I^n`. -/
@[stacks 02O9]
theorem isFiniteType [IsLocallyNoetherian Y] [IsProper f] [F.IsCoherent] :
    GradedModuleSheaf.IsFiniteType.{u, u} (gradedModule I f F p) :=
  sorry

end IdealPowerCohomology
end AlgebraicGeometry.Scheme.Hom
