/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Devissage.FinitePresentation
import StacksCheckRecall

@[expose] public section

universe u

variable {R : Type u} [CommRing R] {S : FGAlgCat.{u} R}
variable {N : FGModuleCat.{u} S.obj} {r : PrimeSpectrum R}
variable (D : Module.Devissage.Complete R S N r)
variable [Algebra.FinitePresentation R S.obj]

/- Remark 38.6.3: assuming `S` is finitely presented over `R`, finite presentation of the
source module over `S`, of the initial module over `A₀`, of its restriction to `B₀`, and of
every stage module over both `Aᵢ` and `Bᵢ` are equivalent. -/
@[stacks 05HY]
#check
  (Module.Devissage.Complete.finitePresentation_tfae D :
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
      ])

#check
  (Module.Devissage.Complete.finitePresentationB D :
    ∀ i : Fin (D.last + 1), Algebra.FinitePresentation R (D.stage i).B)

#check
  (Module.Devissage.Complete.finitePresentationASucc D :
    ∀ i : Fin D.last, Algebra.FinitePresentation R (D.stage i.succ).A)

#check
  (Module.Devissage.Complete.finitePresentationAFirst D :
    Algebra.FinitePresentation R (D.stage 0).A)

#check
  (Module.Devissage.Complete.toA_finitePresentation D :
    ∀ i : Fin (D.last + 1),
      RingHom.FinitePresentation (D.stage i).toA.hom.toRingHom)
