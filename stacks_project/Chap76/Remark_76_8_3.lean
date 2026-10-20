/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine
import StacksCheckRecall

/-!
# Universal homeomorphisms need not be representable, nor induce étale-site equivalences

Remark 76.8.3 records the affine-line-with-zero-doubled counterexample.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Remark 76.8.3: the universal homeomorphism of the affine-line involution space is not relatively representable. -/
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.not_relativelyRepresentable_toAffineLine :
    ∀ (k : Type u) [Field k] [NeZero (2 : k)],
      ¬ uliftYoneda.{u + 1}.relativelyRepresentable
          (AffineLineInvolution.toAffineLine k).hom)

/- Remark 76.8.3: pullback along a universal homeomorphism need not induce an equivalence of spaces-étale sites. -/
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.not_spacesEtalePullback_isEquivalence_of_universalHomeomorphism :
    ¬ ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
        [UniversalHomeomorphism f], (spacesEtalePullback f).IsEquivalence)

namespace DoubledAffineLine

/- Remark 76.8.3: the doubled affine line and its base scheme. -/
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine.base :
    ∀ (k : Type u) [Field k], Scheme.{u})
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine.doubledScheme :
    ∀ (k : Type u) [Field k], Scheme.{u})

/- Remark 76.8.3: the doubled affine-line chart compatibility and cover. -/
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine.chartMap_w :
    ∀ (k : Type u) [Field k] (i : Fin 2),
      DoubleAlong.chartMap (AffineLineInvolution.puncturedOpen k) i ≫
          DoubleAlong.fold (AffineLineInvolution.puncturedOpen k) ≫
            (AffineLineInvolution.cover k).hom =
        (AffineLineInvolution.cover k).hom)
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine.cover :
    ∀ (k : Type u) [Field k], Over (base k))
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine.cover_left :
    ∀ (k : Type u) [Field k], (cover k).left = doubledScheme k)
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine.cover_hom :
    ∀ (k : Type u) [Field k],
      (cover k).hom =
        DoubleAlong.fold (AffineLineInvolution.puncturedOpen k) ≫
          (AffineLineInvolution.cover k).hom)
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine.chartHom :
    ∀ (k : Type u) [Field k] (i : Fin 2),
      AffineLineInvolution.cover k ⟶ cover k)
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine.chartHom_left :
    ∀ (k : Type u) [Field k] (i : Fin 2),
      (chartHom k i).left =
        DoubleAlong.chartMap (AffineLineInvolution.puncturedOpen k) i)
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine.chartCoproduct :
    ∀ (k : Type u) [Field k], Over (base k))
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine.atlasCoproduct :
    ∀ (k : Type u) [Field k], chartCoproduct k ⟶ cover k)
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine.toAffineCoproduct :
    ∀ (k : Type u) [Field k], chartCoproduct k ⟶ AffineLineInvolution.cover k)

/- Remark 76.8.3: the glued atlas morphism and its chart restrictions. -/
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine.atlasHom :
    ∀ (k : Type u) [Field k], Type (u + 1))
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine.ChartRestrictions :
    ∀ {k : Type u} [Field k], atlasHom k → Prop)
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine.ChartRestrictions.of :
    ∀ {k : Type u} [Field k] (f : atlasHom k),
      ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (chartHom k 0) ≫ f =
        AffineLineInvolution.atlas k) →
      ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (chartHom k 1) ≫ f =
        (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
            (AffineLineInvolution.involution k) ≫
          AffineLineInvolution.atlas k) →
      ChartRestrictions f)
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine.ChartRestrictions.iff :
    ∀ {k : Type u} [Field k] (f : atlasHom k),
      ChartRestrictions f ↔
        (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (chartHom k 0) ≫ f =
            AffineLineInvolution.atlas k ∧
          (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (chartHom k 1) ≫ f =
            (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
                (AffineLineInvolution.involution k) ≫
              AffineLineInvolution.atlas k)
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine.existsUnique_atlasHom :
    ∀ (k : Type u) [Field k] [NeZero (2 : k)],
      ∃! f : atlasHom k, ChartRestrictions f)
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine.atlasSquare_isPullback :
    ∀ (k : Type u) [Field k] [NeZero (2 : k)]
      (f : atlasHom k) (hf : ChartRestrictions f),
      IsPullback
        ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (atlasCoproduct k))
        ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (toAffineCoproduct k))
        f (AffineLineInvolution.atlas k))

/- Remark 76.8.3: finite étale and finite locally free properties of the cover. -/
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine.isIso_of_connected_finiteEtale :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
      {U : Over (base k)} (f : U ⟶ AffineLineInvolution.cover k)
      [AlgebraicGeometry.IsFinite f.left] [AlgebraicGeometry.Etale f.left]
      [AlgebraicGeometry.Surjective f.left] [ConnectedSpace U.left],
      IsIso f)
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine.finiteEtale_atlasHom :
    ∀ (k : Type u) [Field k] [CharZero k]
      (f : atlasHom k) (hf : ChartRestrictions f),
      (MorphismProperty.over
          (@AlgebraicGeometry.IsFinite ⊓ @AlgebraicGeometry.Etale)).relative
        uliftYoneda.{u + 1} f.hom)
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine.finiteLocallyFreeOfRank_atlasHom :
    ∀ (k : Type u) [Field k] [CharZero k]
      (f : atlasHom k) (hf : ChartRestrictions f),
      (MorphismProperty.over
          ((fun _ _ g ↦ IsFiniteLocallyFreeOfRank g 2) :
            MorphismProperty Scheme.{u})).relative
        uliftYoneda.{u + 1} f.hom)
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine.finiteLocallyFreeOfRank_toAffineCoproduct :
    ∀ (k : Type u) [Field k] [CharZero k],
      IsFiniteLocallyFreeOfRank (toAffineCoproduct k).left 2)
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine.connected_cover :
    ∀ (k : Type u) [Field k], ConnectedSpace (cover k).left)
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine.not_isIso_atlasHom :
    ∀ (k : Type u) [Field k] [CharZero k]
      (f : atlasHom k) (hf : ChartRestrictions f),
      ¬ IsIso f)

/- Remark 76.8.3: the involution-space morphism to the affine line is universally homeomorphic. -/
@[stacks 05ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.universalHomeomorphism_toAffineLine :
    ∀ (k : Type u) [Field k] [NeZero (2 : k)],
      AlgebraicGeometry.AlgebraicSpace.Sheaf.isUniversalHomeomorphism
        (AffineLineInvolution.toAffineLine k))

end DoubledAffineLine
end AlgebraicGeometry.AlgebraicSpace
