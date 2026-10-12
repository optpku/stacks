/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap35.Lemma_35_8_7_AssociatedModule
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Quasicoherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/- Lemma 35.8.7 (1): the associated module is quasi-coherent on each of the five
canonical big standard sites. -/
@[stacks 03DV] #check
  (AlgebraicGeometry.StandardTopology.Big.associatedModule_isQuasicoherent :
    ∀ (τ : StandardTopology) (S : Scheme.{u})
      (F : S.Modules) [F.IsQuasicoherent],
      (AlgebraicGeometry.StandardTopology.Big.associatedModule τ S F).IsQuasicoherent)

/- Lemma 35.8.7 (2): the associated modules are quasi-coherent on both the canonical
small Zariski and small étale sites. -/
@[stacks 03DV] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.small_isQuasicoherent :
    ∀ (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent],
      (AlgebraicGeometry.Scheme.Zariski.Small.associatedModule S F).IsQuasicoherent ∧
        (AlgebraicGeometry.Scheme.Etale.Small.associatedModule S F).IsQuasicoherent)

end AlgebraicGeometry.Scheme.AssociatedModule
