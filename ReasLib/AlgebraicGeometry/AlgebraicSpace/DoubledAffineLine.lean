/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.TopologicalInvariance
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic

/-!
# The doubled affine line and its étale cover

This module defines the affine line with zero doubled by gluing two copies of `𝔸¹_k`
along `D(x)`, together with its two affine charts and the comparison `1 ⨿ (-1)`
toward `𝔸¹_k`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine

/-- The base scheme `S = Spec k`. -/
abbrev base (k : Type u) [Field k] : Scheme.{u} := AffineLineInvolution.base k

/-- The affine line with zero doubled, as a scheme. -/
abbrev doubledScheme (k : Type u) [Field k] : Scheme.{u} :=
  doubleAlong (AffineLineInvolution.puncturedOpen k)

/-- Each canonical chart of the doubled line is compatible with the structure morphism. -/
theorem chartMap_w (k : Type u) [Field k] (i : Fin 2) :
    DoubleAlong.chartMap (AffineLineInvolution.puncturedOpen k) i ≫
        DoubleAlong.fold (AffineLineInvolution.puncturedOpen k) ≫
          (AffineLineInvolution.cover k).hom =
      (AffineLineInvolution.cover k).hom := sorry

/-- The affine line with zero doubled, as a scheme over `Spec k`. -/
def cover (k : Type u) [Field k] : Over (base k) :=
  Over.mk (DoubleAlong.fold (AffineLineInvolution.puncturedOpen k) ≫
    (AffineLineInvolution.cover k).hom)

/-- The underlying scheme of `cover k` is the doubled affine line. -/
theorem cover_left (k : Type u) [Field k] :
    (cover k).left = doubledScheme k := sorry

/-- The structure morphism of `cover k` is the fold followed by `𝔸¹_k ⟶ Spec k`. -/
theorem cover_hom (k : Type u) [Field k] :
    (cover k).hom =
      DoubleAlong.fold (AffineLineInvolution.puncturedOpen k) ≫
        (AffineLineInvolution.cover k).hom := sorry

/-- The open immersion of the `i`-th affine-line chart into the doubled line, over `Spec k`. -/
def chartHom (k : Type u) [Field k] (i : Fin 2) :
    AffineLineInvolution.cover k ⟶ cover k :=
  Over.homMk (DoubleAlong.chartMap (AffineLineInvolution.puncturedOpen k) i)
    (chartMap_w k i)

/-- The underlying scheme map of `chartHom k i` is the canonical doubled-scheme chart map. -/
theorem chartHom_left (k : Type u) [Field k] (i : Fin 2) :
    (chartHom k i).left =
      DoubleAlong.chartMap (AffineLineInvolution.puncturedOpen k) i := sorry

/-- The coproduct of the two affine-line charts, as a scheme over `Spec k`. -/
def chartCoproduct (k : Type u) [Field k] : Over (base k) :=
  AffineLineInvolution.cover k ⨿ AffineLineInvolution.cover k

/-- The two chart immersions, as a morphism from the coproduct of charts to `Y`. -/
def atlasCoproduct (k : Type u) [Field k] : chartCoproduct k ⟶ cover k :=
  coprod.desc (chartHom k 0) (chartHom k 1)

/-- The map `1 ⨿ (-1)` from the coproduct of charts to `𝔸¹_k`. -/
def toAffineCoproduct (k : Type u) [Field k] :
    chartCoproduct k ⟶ AffineLineInvolution.cover k :=
  coprod.desc (𝟙 _) (AffineLineInvolution.involution k)


end AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine

namespace AlgebraicGeometry.AlgebraicSpace

/-- The universal homeomorphism from the affine-line involution space to the affine line
is not relatively representable. -/
theorem AffineLineInvolution.not_relativelyRepresentable_toAffineLine
    (k : Type u) [Field k] [NeZero (2 : k)] :
    ¬ uliftYoneda.{u + 1}.relativelyRepresentable
        (AffineLineInvolution.toAffineLine k).hom :=
  sorry

/-- Pullback along a universal homeomorphism of algebraic spaces need not induce an
equivalence of spaces-étale sites. -/
theorem not_spacesEtalePullback_isEquivalence_of_universalHomeomorphism :
    ¬ ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
        [UniversalHomeomorphism f], (spacesEtalePullback f).IsEquivalence :=
  sorry

namespace DoubledAffineLine


/-- The type of morphisms of fppf sheaves from the doubled affine line `Y` to the
involution space `X`. -/
abbrev atlasHom (k : Type u) [Field k] :=
  (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (cover k) ⟶
    AffineLineInvolution.sheafOfPoints k

/-- The chart restrictions used to glue a morphism from the doubled affine line to the
involution space: the identity on the first
affine chart and `x ↦ -x` on the second. -/
structure ChartRestrictions {k : Type u} [Field k] (f : atlasHom k) : Prop where
  /-- The first chart restricts to the atlas `𝔸¹_k ⟶ X`. -/
  chart0 :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (chartHom k 0) ≫ f =
      AffineLineInvolution.atlas k
  /-- The second chart restricts to negation followed by the atlas `𝔸¹_k ⟶ X`. -/
  chart1 :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (chartHom k 1) ≫ f =
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
          (AffineLineInvolution.involution k) ≫
        AffineLineInvolution.atlas k

/-- Package the two chart restrictions of a morphism `Y ⟶ X`. -/
def ChartRestrictions.of {k : Type u} [Field k] (f : atlasHom k)
    (chart0 :
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (chartHom k 0) ≫ f =
        AffineLineInvolution.atlas k)
    (chart1 :
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (chartHom k 1) ≫ f =
        (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
            (AffineLineInvolution.involution k) ≫
          AffineLineInvolution.atlas k) :
    ChartRestrictions f :=
  ⟨chart0, chart1⟩

/-- `ChartRestrictions f` is equivalent to its two chart identities. -/
theorem ChartRestrictions.iff {k : Type u} [Field k] (f : atlasHom k) :
    ChartRestrictions f ↔
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (chartHom k 0) ≫ f =
          AffineLineInvolution.atlas k ∧
        (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (chartHom k 1) ≫ f =
          (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
              (AffineLineInvolution.involution k) ≫
            AffineLineInvolution.atlas k :=
  sorry

/-- If `k` is algebraically closed of characteristic zero, then `𝔸¹_k`
has no nontrivial connected finite étale covering. -/
@[stacks 05ZI]
theorem isIso_of_connected_finiteEtale
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    {U : Over (base k)} (f : U ⟶ AffineLineInvolution.cover k)
    [AlgebraicGeometry.IsFinite f.left] [AlgebraicGeometry.Etale f.left]
    [AlgebraicGeometry.Surjective f.left] [ConnectedSpace U.left] :
    IsIso f :=
  sorry

/-- The two chart restrictions glue uniquely to a morphism from the doubled affine line to the involution space. -/
@[stacks 05ZI]
theorem existsUnique_atlasHom (k : Type u) [Field k] [NeZero (2 : k)] :
    ∃! f : atlasHom k, ChartRestrictions f :=
  sorry

/-- For a morphism glued from the two charts, the square with vertices `Y`,
`Y₁ ⨿ Y₂`, `X`, and `𝔸¹_k` is cartesian. -/
@[stacks 05ZI]
theorem atlasSquare_isPullback (k : Type u) [Field k] [NeZero (2 : k)]
    (f : atlasHom k) (hf : ChartRestrictions f) :
    IsPullback
      ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (atlasCoproduct k))
      ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (toAffineCoproduct k))
      f (AffineLineInvolution.atlas k) :=
  sorry

/-- A morphism glued from the two charts is finite étale. -/
@[stacks 05ZI]
theorem finiteEtale_atlasHom (k : Type u) [Field k] [CharZero k]
    (f : atlasHom k) (hf : ChartRestrictions f) :
    (MorphismProperty.over
        (@AlgebraicGeometry.IsFinite ⊓ @AlgebraicGeometry.Etale)).relative
      uliftYoneda.{u + 1} f.hom :=
  sorry

/-- A morphism glued from the two charts is finite locally free of rank `2`
relative to `uliftYoneda`. -/
@[stacks 05ZI]
theorem finiteLocallyFreeOfRank_atlasHom
    (k : Type u) [Field k] [CharZero k]
    (f : atlasHom k) (hf : ChartRestrictions f) :
    (MorphismProperty.over
        ((fun _ _ g ↦ IsFiniteLocallyFreeOfRank g 2) :
          MorphismProperty Scheme.{u})).relative
      uliftYoneda.{u + 1} f.hom :=
  sorry

/-- The comparison `1 ⨿ (-1) : 𝔸¹_k ⨿ 𝔸¹_k ⟶ 𝔸¹_k` is finite locally free of rank `2`. -/
theorem finiteLocallyFreeOfRank_toAffineCoproduct
    (k : Type u) [Field k] [CharZero k] :
    IsFiniteLocallyFreeOfRank (toAffineCoproduct k).left 2 :=
  sorry

/-- The doubled affine line is connected. -/
@[stacks 05ZI]
theorem connected_cover (k : Type u) [Field k] :
    ConnectedSpace (cover k).left :=
  sorry

/-- A morphism glued from the two charts is nontrivial. -/
@[stacks 05ZI]
theorem not_isIso_atlasHom (k : Type u) [Field k] [CharZero k]
    (f : atlasHom k) (hf : ChartRestrictions f) :
    ¬ IsIso f :=
  sorry



end DoubledAffineLine

end AlgebraicGeometry.AlgebraicSpace
