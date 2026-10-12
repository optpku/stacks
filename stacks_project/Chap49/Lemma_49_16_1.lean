/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein.QuasiFinite

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 49.16.1: for a quasi-finite morphism `f : Y ⟶ X` of Noetherian
schemes and a relative dualizing sheaf `W`, the following are equivalent:
`f` is Gorenstein; `f` is flat with Gorenstein fibres; `f` is flat and
`W.module.obj` is invertible; and, locally on affine opens around every point of
`Y`, the induced section-ring map is flat and the presented relative dualizing
module is invertible. -/
@[stacks 0C16] #check (AlgebraicGeometry.quasiFiniteGorenstein_tfae :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [IsNoetherian X] [IsNoetherian Y]
      [Scheme.Hom.QuasiFinite f] (W : f.RelativeDualizingSheaf),
      List.TFAE [
        Gorenstein f,
        Flat f ∧ ∀ x : X, Scheme.Gorenstein (f.fiber x),
        Flat f ∧ Scheme.Modules.Invertible W.module.obj,
        ∀ y : Y, ∃ V : Y.affineOpens, y ∈ (V : Y.Opens) ∧
          ∃ U : X.affineOpens, ∃ e : V ≤ f ⁻¹ᵁ U,
            (f.appLE U V e).hom.Flat ∧
              Module.Invertible Γ(Y, V)
                ((W.presentation U V e).module
                  (IsLocallyNoetherian.component_noetherian U)
                  (IsLocallyNoetherian.component_noetherian V)
                  (f.affineQuasiFinite U V e))])
