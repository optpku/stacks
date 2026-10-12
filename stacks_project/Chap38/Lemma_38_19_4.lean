/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.EtaleFreeOpen

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 38.19.4: for a locally finite-type morphism `f : X ⟶ S` and a finite-type
quasicoherent module `F` flat at `x` over `S`, there is an affine elementary étale
neighbourhood of `f x` and an affine open in the local base change containing the induced
point on which the restricted sections form a free module over the stalk ring. -/
@[stacks 05MF] #check
  (AlgebraicGeometry.Scheme.Modules.existsAffineOpenWithFreeSections :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
      (x : X), flatOverAt F f x →
    ∃ U : EtaleNeighborhood.Elementary S (f x),
      let E := U.obj
      let T := E.toEtale.left
      let R := T.presheaf.stalk E.point
      let b := T.fromSpecStalk E.point ≫ E.toEtale.hom
      let P := Limits.pullback f b
      ∃ _ : IsAffine T,
        let F' := baseChangeModule f b F
        ∃ x' : P,
          Limits.pullback.fst f b x' = x ∧
            Limits.pullback.snd f b x' = IsLocalRing.closedPoint R ∧
              ∃ V : P.Opens, x' ∈ V ∧ IsAffineOpen V ∧
                Module.Free R
                  (Scheme.Hom.sectionsModOverSpec (Limits.pullback.snd f b) V
                    F' : ModuleCat R))

end AlgebraicGeometry.Scheme.Modules
