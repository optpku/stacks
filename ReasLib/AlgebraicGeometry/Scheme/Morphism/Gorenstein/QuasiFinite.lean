/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.Invertible

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- For a quasi-finite morphism of Noetherian schemes, Gorensteinness,
flatness with Gorenstein fibres, invertibility of a relative dualizing sheaf,
and the corresponding affine criterion are equivalent. -/
theorem quasiFiniteGorenstein_tfae
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsNoetherian X] [IsNoetherian Y]
    [Scheme.Hom.QuasiFinite f] (W : f.RelativeDualizingSheaf) :
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
                (f.affineQuasiFinite U V e))] := sorry

end AlgebraicGeometry
