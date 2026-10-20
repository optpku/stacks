/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.EtaleFree
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 38.12.10: a finite-presentation morphism and finite-type quasicoherent
module, flat at every point of a fibre, admit an elementary etale base neighbourhood
and an affine finite-presentation etale refinement whose pulled-back module is finitely
presented with free global sections, and which covers exactly the original fibre. -/
@[stacks 05L0]
#check (AlgebraicGeometry.Scheme.Modules.existsEtaleCoverWithFreeSections :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S),
    [Scheme.Hom.FinitePresentation f] →
    ∀ (F : X.Modules), [F.IsQuasicoherent] → [F.IsFiniteType] →
    ∀ (s : S), (∀ x : f.fiber s, flatOverAt F f (f.fiberι s x)) →
      ∃ U : EtaleNeighborhood.Elementary S s,
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
          let F' := (Scheme.Modules.pullback g).obj F
          ∃ (_ : Set.range (f.fiberι s) = Set.range (p.fiberι x₀ ≫ g))
            (_ : IsAffine X') (_ : Scheme.Hom.FinitePresentation p)
            (_ : F'.IsFinitePresentation),
            Module.Free R (Scheme.Hom.globalSectionsMod p F' : ModuleCat R))

end AlgebraicGeometry.Scheme.Modules
