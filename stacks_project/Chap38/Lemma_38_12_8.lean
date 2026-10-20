module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.EtaleFree
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 38.12.8: a finite-type quasicoherent module flat at a point over a locally
finitely presented morphism becomes finitely presented with free global sections after
an elementary étale refinement of the base and an affine étale refinement of the source. -/
@[stacks 05KY] #check
  (AlgebraicGeometry.Scheme.Modules.existsEtaleRefinementWithFreeSections :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
      (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
      (x : X) (h_flat : flatOverAt F f x),
      ∃ U : EtaleNeighborhood.Elementary S (f x),
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
          ∃ x' : X',
            ∃ (_ : g x' = x) (_ : p x' = x₀) (_ : IsIso (g.residueFieldMap x'))
              (_ : IsAffine X') (_ : Scheme.Hom.FinitePresentation p)
              (_ : F'.IsFinitePresentation),
              Module.Free R (Scheme.Hom.globalSectionsMod p F' : ModuleCat R))

end AlgebraicGeometry.Scheme.Modules
