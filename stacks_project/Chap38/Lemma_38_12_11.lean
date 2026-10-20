/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.EtaleFree
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 38.12.11: a finite-type morphism and finite-type quasicoherent module,
flat at every point of a fibre, admit an elementary étale base neighbourhood and an
affine étale refinement whose pulled-back module has free global sections and which
covers exactly the original fibre. -/
@[stacks 05L1] #check
  (AlgebraicGeometry.Scheme.Modules.existsEtaleCoverWithFreeSections_of_finiteType :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FiniteType f]
      (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
      (s : S) (h_flat : ∀ x : f.fiber s,
        AlgebraicGeometry.Scheme.Modules.flatOverAt F f (f.fiberι s x)),
      ∃ U : AlgebraicGeometry.Scheme.EtaleNeighborhood.Elementary S s,
        let E := U.obj
        let T := E.toEtale.left
        let R := T.presheaf.stalk E.point
        let b := T.fromSpecStalk E.point ≫ E.toEtale.hom
        let P := Limits.pullback f b
        ∃ Y : P.Etale,
          let X' := Y.left
          let g := Y.hom ≫ Limits.pullback.fst f b
          let p := Y.hom ≫ Limits.pullback.snd f b
          let x₀ := IsLocalRing.closedPoint R
          let F' := (AlgebraicGeometry.Scheme.Modules.pullback g).obj F
          ∃ (_ : Set.range (f.fiberι s) = Set.range (p.fiberι x₀ ≫ g))
            (_ : AlgebraicGeometry.IsAffine X'),
            Module.Free R (AlgebraicGeometry.Scheme.Hom.globalSectionsMod p F' : ModuleCat R))

end AlgebraicGeometry.Scheme.Modules
