/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.SmallEtaleQuasicoherent
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace AlgebraicGeometry
namespace Scheme
namespace AssociatedModule
namespace SmallEtaleQuasicoherent

/- Lemma 35.10.3 (1): a coproduct of quasi-coherent modules on the small étale
site is quasi-coherent. -/
@[stacks 0GNB]
#check
  (AlgebraicGeometry.Scheme.AssociatedModule.SmallEtaleQuasicoherent.coproduct :
    ∀ (S : Scheme.{u}) {ι : Type v}
      (F : ι → SheafOfModules (smallStructureSheaf .etale S))
      [HasCoproduct F] [∀ i, (F i).IsQuasicoherent],
      (∐ F).IsQuasicoherent)

/- Lemma 35.10.3 (2): quasi-coherent modules on the small étale site are
closed under colimits of every universe-compatible shape. -/
@[stacks 0GNB]
#check
  (AlgebraicGeometry.Scheme.AssociatedModule.SmallEtaleQuasicoherent.closedUnderColimitsOfShape :
    ∀ (S : Scheme.{u}) (J : Type v) [Category.{w} J],
      IsClosedUnderColimitsOfShape
        (SheafOfModules.isQuasicoherent (smallStructureSheaf .etale S)) J)

/- Lemma 35.10.3 (3)-(4): quasi-coherent modules on the small étale site form
a weak Serre class, giving closure under kernels, cokernels, and every
short-exact two-out-of-three implication. -/
@[stacks 0GNB]
#check
  (AlgebraicGeometry.Scheme.AssociatedModule.SmallEtaleQuasicoherent.isWeakSerreClass :
    ∀ (S : Scheme.{u}),
      IsWeakSerreClass
        (SheafOfModules.isQuasicoherent
          (smallCommRingedSite .etale S).structureSheaf))

variable (S : Scheme.{u})
variable (F G : RingedSite.ModuleCat.{u + 1} (smallCommRingedSite .etale S))
variable [F.IsQuasicoherent] [G.IsQuasicoherent]

/- Lemma 35.10.3 (5): the tensor product of two quasi-coherent modules on the
small étale site is quasi-coherent. -/
@[stacks 0GNB]
#check (SheafOfModules.IsQuasicoherent.tensor F G :
  (SheafOfModules.RingedSite.moduleTensor F G).IsQuasicoherent)

/- Lemma 35.10.3 (6): internal Hom from a finitely presented module to a
quasi-coherent module on the small étale site is quasi-coherent. -/
@[stacks 0GNB]
#check
  (AlgebraicGeometry.Scheme.AssociatedModule.SmallEtaleQuasicoherent.internalHom :
    ∀ (S : Scheme.{u})
      (F G : RingedSite.ModuleCat.{u + 1} (smallCommRingedSite .etale S))
      [F.IsFinitePresentation] [G.IsQuasicoherent],
      ((ihom F).obj G).IsQuasicoherent)

end SmallEtaleQuasicoherent
end AssociatedModule
end Scheme
end AlgebraicGeometry
