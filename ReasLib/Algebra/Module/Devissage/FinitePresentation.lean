/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import ReasLib.Algebra.Module.Devissage.Complete
public import ReasLib.Algebra.Module.FinitePresentation.RestrictScalars

/-!
# Finite presentation in complete module dévissages

This file records finite-presentation properties of the algebras, comparison maps, and modules
appearing in a complete module dévissage.
-/

@[expose] public section

universe u

namespace Module.Devissage.Complete

variable {R : Type u} [CommRing R] {S : FGAlgCat.{u} R}
variable {N : FGModuleCat.{u} S.obj} {r : PrimeSpectrum R}

/-- Every intermediate algebra `Bᵢ` in a complete dévissage is finitely presented over `R`. -/
theorem finitePresentationB (D : Complete R S N r) (i : Fin (D.last + 1)) :
    Algebra.FinitePresentation R (D.stage i).B := sorry

/-- If `S` is finitely presented over `R`, then the initial algebra `A₀` is finitely presented
over `R`. -/
theorem finitePresentationAFirst (D : Complete R S N r)
    [Algebra.FinitePresentation R S.obj] :
    Algebra.FinitePresentation R (D.stage 0).A := sorry

/-- Every noninitial algebra `Aᵢ` in a complete dévissage is finitely presented over `R`. -/
theorem finitePresentationASucc (D : Complete R S N r) (i : Fin D.last) :
    Algebra.FinitePresentation R (D.stage i.succ).A := sorry

/-- If `S` is finitely presented over `R`, then every stage map `Bᵢ ⟶ Aᵢ` is a ring map of
finite presentation. -/
theorem toA_finitePresentation (D : Complete R S N r)
    [Algebra.FinitePresentation R S.obj] (i : Fin (D.last + 1)) :
    RingHom.FinitePresentation (D.stage i).toA.hom.toRingHom := sorry

/-- Finite presentation of the source module is equivalent to finite presentation of the
initial-stage module over its `A`-algebra. -/
theorem finitePresentation_iff_firstA (D : Complete R S N r)
    [Algebra.FinitePresentation R S.obj] :
    Module.FinitePresentation S.obj N ↔
      Module.FinitePresentation (D.stage 0).A (D.stage 0).M := sorry

/-- At the initial stage, finite presentation over `A` is equivalent to finite presentation
after restriction of scalars to `B`. -/
theorem firstA_finitePresentation_iff_firstB (D : Complete R S N r)
    [Algebra.FinitePresentation R S.obj] :
    Module.FinitePresentation (D.stage 0).A (D.stage 0).M ↔
      Module.FinitePresentation (D.stage 0).B
        ((ModuleCat.restrictScalars (D.stage 0).toA.hom.toRingHom).obj
          (D.stage 0).M.obj) := sorry

/-- Finite presentation at the initial `A`-stage is equivalent to finite presentation over
both coefficient algebras at every stage. -/
theorem finitePresentation_iff_allStages (D : Complete R S N r)
    [Algebra.FinitePresentation R S.obj] :
    Module.FinitePresentation (D.stage 0).A (D.stage 0).M ↔
      ∀ i : Fin (D.last + 1),
        Module.FinitePresentation (D.stage i).A (D.stage i).M ∧
          Module.FinitePresentation (D.stage i).B
            ((ModuleCat.restrictScalars (D.stage i).toA.hom.toRingHom).obj
              (D.stage i).M.obj) := sorry

/-- If `S` is finitely presented over `R`, finite presentation of the source module over `S`,
of the initial module over `A₀`, of its restriction to `B₀`, and of every stage module over both
`Aᵢ` and `Bᵢ` are equivalent. -/
theorem finitePresentation_tfae (D : Complete R S N r)
    [Algebra.FinitePresentation R S.obj] :
    List.TFAE
      [ Module.FinitePresentation S.obj N
      , Module.FinitePresentation (D.stage 0).A (D.stage 0).M
      , Module.FinitePresentation (D.stage 0).B
          ((ModuleCat.restrictScalars (D.stage 0).toA.hom.toRingHom).obj
            (D.stage 0).M.obj)
      , ∀ i : Fin (D.last + 1),
          Module.FinitePresentation (D.stage i).A (D.stage i).M ∧
            Module.FinitePresentation (D.stage i).B
              ((ModuleCat.restrictScalars (D.stage i).toA.hom.toRingHom).obj
                (D.stage i).M.obj)
      ] := sorry

end Module.Devissage.Complete
