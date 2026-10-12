/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import stacks_project.Chap66.Lemma_66_18_8_Pullback
public import stacks_project.Chap67.Example_67_53_3_Homeomorphism
public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism
public import stacks_project.Chap76.Remark_76_8_3_Action
public import stacks_project.Chap76.Theorem_76_8_1_Equivalence
import StacksCheckRecall

/-!
# Universal homeomorphisms need not be representable, nor induce étale-site equivalences

Remark 76.8.3 records that a universal homeomorphism of algebraic spaces need not be
representable, and that the étale-site invariance of Theorem 76.8.1 fails if the
integral universally bijective hypothesis is weakened to a universal homeomorphism.
The witness is the affine line with zero doubled over an algebraically closed field
of characteristic zero.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Remark 76.8.3 (1): a universal homeomorphism of algebraic spaces need not be
representable. The morphism `X ⟶ 𝔸¹_k` of Morphisms of Spaces, Example 67.53.3 is a
universal homeomorphism which is not relatively representable. -/
@[stacks 05ZI]
theorem AffineLineInvolution.not_relativelyRepresentable_toAffineLine
    (k : Type u) [Field k] [NeZero (2 : k)] :
    ¬ uliftYoneda.{u + 1}.relativelyRepresentable
        (AffineLineInvolution.toAffineLine k).hom :=
  sorry

/-- Remark 76.8.3 (2): Theorem 76.8.1 does not hold for universal homeomorphisms. Pullback
along a universal homeomorphism of algebraic spaces need not induce an equivalence of
spaces-étale sites. -/
@[stacks 05ZI]
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

/-- `atlasHom k` is the Hom-type of fppf sheaf maps `Y ⟶ X`. -/
theorem atlasHom_eq (k : Type u) [Field k] :
    atlasHom k =
      ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (cover k) ⟶
        AffineLineInvolution.sheafOfPoints k) :=
  sorry

/-- The source chart restrictions used to glue `Y ⟶ X`: the identity on the first
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

/-- `ChartRestrictions f` is equivalent to the two source chart identities. -/
theorem ChartRestrictions.iff {k : Type u} [Field k] (f : atlasHom k) :
    ChartRestrictions f ↔
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (chartHom k 0) ≫ f =
          AffineLineInvolution.atlas k ∧
        (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (chartHom k 1) ≫ f =
          (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
              (AffineLineInvolution.involution k) ≫
            AffineLineInvolution.atlas k :=
  sorry

/-- Remark 76.8.3 (3): if `k` is algebraically closed of characteristic zero, then `𝔸¹_k`
has no nontrivial connected finite étale covering. -/
@[stacks 05ZI]
theorem isIso_of_connected_finiteEtale
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    {U : Over (base k)} (f : U ⟶ AffineLineInvolution.cover k)
    [AlgebraicGeometry.IsFinite f.left] [AlgebraicGeometry.Etale f.left]
    [AlgebraicGeometry.Surjective f.left] [ConnectedSpace U.left] :
    IsIso f :=
  sorry

/-- Remark 76.8.3 (4): the two chart restrictions glue uniquely to a morphism `Y ⟶ X`. -/
@[stacks 05ZI]
theorem existsUnique_atlasHom (k : Type u) [Field k] [NeZero (2 : k)] :
    ∃! f : atlasHom k, ChartRestrictions f :=
  sorry

/-- Remark 76.8.3 (5): for the glued morphism `Y ⟶ X`, the square with vertices `Y`,
`Y₁ ⨿ Y₂`, `X`, and `𝔸¹_k` is cartesian. -/
@[stacks 05ZI]
theorem atlasSquare_isPullback (k : Type u) [Field k] [NeZero (2 : k)]
    (f : atlasHom k) (hf : ChartRestrictions f) :
    IsPullback
      ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (atlasCoproduct k))
      ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (toAffineCoproduct k))
      f (AffineLineInvolution.atlas k) :=
  sorry

/-- Remark 76.8.3 (6): the glued morphism `Y ⟶ X` is finite étale. -/
@[stacks 05ZI]
theorem finiteEtale_atlasHom (k : Type u) [Field k] [CharZero k]
    (f : atlasHom k) (hf : ChartRestrictions f) :
    (MorphismProperty.over
        (@AlgebraicGeometry.IsFinite ⊓ @AlgebraicGeometry.Etale)).relative
      uliftYoneda.{u + 1} f.hom :=
  sorry

/-- Remark 76.8.3 (10): the glued morphism `Y ⟶ X` is finite locally free of rank `2`
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

/-- Remark 76.8.3 (7): the scheme `Y` is connected. -/
@[stacks 05ZI]
theorem connected_cover (k : Type u) [Field k] :
    ConnectedSpace (cover k).left :=
  sorry

/-- Remark 76.8.3 (8): the glued covering `Y ⟶ X` is nontrivial. -/
@[stacks 05ZI]
theorem not_isIso_atlasHom (k : Type u) [Field k] [CharZero k]
    (f : atlasHom k) (hf : ChartRestrictions f) :
    ¬ IsIso f :=
  sorry

/- Remark 76.8.3 (9): the morphism `X ⟶ 𝔸¹_k` induced by `t ↦ t²` is a universal
homeomorphism, as in Morphisms of Spaces, Example 67.53.3. -/
@[stacks 05ZI]
#check AffineLineInvolution.universalHomeomorphism_toAffineLine

end DoubledAffineLine

end AlgebraicGeometry.AlgebraicSpace
