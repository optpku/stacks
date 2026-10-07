module

public import stacks_project.Chap66.Lemma_66_29_7_CommSheaf
public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.MonoidalClosed CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.29.7 (1): a coproduct of quasi-coherent modules on an algebraic space is
quasi-coherent. -/
@[stacks 03M1]
#check
  (Modules.isQuasicoherent_coproduct :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) {ι : Type v}
      (F : ι → X.Modules) [HasCoproduct F] [∀ i, (F i).IsQuasicoherent],
      (∐ F).IsQuasicoherent)

/- Lemma 66.29.7 (2): quasi-coherent modules on an algebraic space are closed under
colimits of every universe-compatible shape. -/
@[stacks 03M1]
#check
  (QCoh.closedUnderColimitsOfShape :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (J : Type v) [Category.{w} J],
      (quasiCoherentModuleProperty X).IsClosedUnderColimitsOfShape J)

/- Lemma 66.29.7 (3): the kernel and cokernel of a morphism of quasi-coherent modules on
an algebraic space are quasi-coherent. -/
@[stacks 03M1]
#check
  (Modules.isQuasicoherent_kernel :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {F G : X.Modules}
      [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G),
      (kernel f).IsQuasicoherent)

@[stacks 03M1]
#check
  (Modules.isQuasicoherent_cokernel :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {F G : X.Modules}
      [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G),
      (cokernel f).IsQuasicoherent)

/- Lemma 66.29.7 (4): in a short exact sequence of modules on an algebraic space, if two
of the three terms are quasi-coherent then so is the third. -/
@[stacks 03M1]
#check
  (QCoh.isWeakSerreClass :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
      (quasiCoherentModuleProperty X).IsWeakSerreClass)

/- Lemma 66.29.7 (5): the tensor product of two quasi-coherent modules on an algebraic
space is quasi-coherent. -/
@[stacks 03M1]
#check
  (Modules.isQuasicoherent_tensor :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (F G : RingedSite.ModuleCat.{u} (commRingedSite X))
      [F.IsQuasicoherent] [G.IsQuasicoherent],
      (SheafOfModules.RingedSite.moduleTensor F G).IsQuasicoherent)

/- Lemma 66.29.7 (6): internal Hom from a finitely presented module to a quasi-coherent
module on an algebraic space is quasi-coherent. -/
@[stacks 03M1]
#check
  (Modules.isQuasicoherent_internalHom :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (F G : RingedSite.ModuleCat.{u + 1} (commRingedSiteLift X))
      [F.IsFinitePresentation] [G.IsQuasicoherent],
      ((ihom F).obj G).IsQuasicoherent)

end AlgebraicGeometry.AlgebraicSpace
