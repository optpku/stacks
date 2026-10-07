module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.DifferentialOperator.ExternalTensor

open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 29.33.2: an order-`k` differential operator on `X/S` extends uniquely to the external
tensor product on `X ×_S Y`, relative to `Y`, and acts on local pure tensors through the given
operator on the first factor. -/
@[stacks 0G45] #check
  (AlgebraicGeometry.Scheme.Modules.DifferentialOperator.existsUnique_externalTensorProductRight :
    ∀ {X S Y : AlgebraicGeometry.Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
      (F F' : X.Modules) [F.IsQuasicoherent] [F'.IsQuasicoherent]
      (G : Y.Modules) [G.IsQuasicoherent] (k : ℕ)
      (D : Diff(a.toShHom ; k ; F, F')),
      ∃! D' : Diff((Limits.pullback.snd a b).toShHom ; k ;
        AlgebraicGeometry.Scheme.Modules.externalTensorProduct a b F G,
        AlgebraicGeometry.Scheme.Modules.externalTensorProduct a b F' G),
        AlgebraicGeometry.Scheme.Modules.DifferentialOperator.IsExternalTensorProductRight
          a b G D D')
