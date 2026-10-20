/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Integral
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 28.22.13 (1): an integral quasi-coherent algebra on a quasi-compact quasi-separated
scheme is the directed colimit of its finite quasi-coherent subalgebras. -/
@[stacks 0817] #check
  (AlgebraicGeometry.Scheme.QcAlgebraUnder.finiteQuasiCoherentSubalgebras_isDirectedColimit_of_isIntegral :
    ∀ {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
      (A : S.QcAlgebraUnder),
      AlgebraicGeometry.Scheme.QcAlgebraUnder.IsIntegral A →
        DirectedOn (· ≤ ·)
            (AlgebraicGeometry.Scheme.QcAlgebraUnder.finiteQuasiCoherentSubalgebras A) ∧
          IsLUB
            (AlgebraicGeometry.Scheme.QcAlgebraUnder.finiteQuasiCoherentSubalgebras A)
            (⊤ : Subobject A.obj))

/- Lemma 28.22.13 (2): an integral quasi-coherent algebra on a quasi-compact quasi-separated
scheme is a filtered colimit of finite and finitely presentable quasi-coherent algebras. -/
@[stacks 0817] #check
  (AlgebraicGeometry.Scheme.QcAlgebraUnder.finiteFinitelyPresentable_ind_of_isIntegral :
    ∀ {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
      (A : S.QcAlgebraUnder),
      AlgebraicGeometry.Scheme.QcAlgebraUnder.IsIntegral A →
        ObjectProperty.ind.{u}
          (fun B : Under (AlgebraicGeometry.Scheme.schemeCommRingSheaf S) ↦
          AlgebraicGeometry.Scheme.QcAlgebraUnder.finiteProperty S B ∧
            AlgebraicGeometry.Scheme.QcAlgebraUnder.finitelyPresentableProperty S B) A.obj)

end
