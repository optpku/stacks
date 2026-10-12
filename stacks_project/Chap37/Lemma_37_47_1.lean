/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.SmoothFactorization
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.47.1: a locally finite type morphism whose fibre has dimension `n` at `x`
admits, after an elementary étale neighbourhood of `x`, a finite factorization through a
morphism smooth of relative dimension `n`. The distinguished fibre is a singleton, its
residue-field extension over `f x` is purely transcendental, and the finite map is of finite
presentation whenever the original morphism is locally of finite presentation. -/
@[stacks 052E] #check
  (AlgebraicGeometry.Scheme.Hom.exists_finite_smoothFactorization :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) (n : ℕ),
      f.fiberDimensionAt x = (n : WithBot ℕ∞) →
        ∃ U : EtaleNeighborhood.Elementary X x,
          let E := U.obj
          ∃ (Y : Scheme.{u}) (π : E.toEtale.left ⟶ Y) (h : Y ⟶ S),
          let y := π E.point
          ∃ (_ : E.toEtale.hom ≫ f = π ≫ h)
            (_ : SmoothOfRelativeDimension n h)
            (_ : IsFinite π)
            (_ : π ⁻¹' {y} = {E.point})
            (hy : h y = f x)
            (_ : ((S.residueFieldCongr hy).inv ≫
              h.residueFieldMap y).hom.IsPurelyTranscendental),
            LocallyOfFinitePresentation f → Scheme.Hom.FinitePresentation π)

end AlgebraicGeometry.Scheme.Hom
