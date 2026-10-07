module

public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.RepresentedBy
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Lemma_67_22_5_EtaleLocal
public import stacks_project.Chap67.Remark_67_22_3_EtaleLocal
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.22.7 (1): if `P` is étale local on source-and-target for scheme
morphisms, then the associated germ-morphism property `representedBy P` is
étale local on source-and-target. -/
@[stacks 04RF] #check
  (Scheme.Germ.MorphismProperty.representedBy_isEtaleLocal :
    (P : MorphismProperty Scheme.{u}) →
      [IsEtaleLocalAtSourceAndTarget P] →
        Scheme.Germ.MorphismProperty.IsEtaleLocal
          (Scheme.Germ.MorphismProperty.representedBy P))

namespace AlgebraicGeometry.AlgebraicSpace

open Scheme.Germ.MorphismProperty

/-- Lemma 67.22.7 (2): let `P` be étale local on source-and-target for scheme
morphisms, and let `Q` be the associated germ-morphism property
`representedBy P`. For a morphism `f : X ⟶ Y` of algebraic spaces and a
point `x` of `|X|`, `f` has `Q` at `x` if and only if there is an open
neighbourhood `X' ⊂ X` of `x` such that `X' ⟶ Y` has `etaleLocal P`. -/
@[stacks 04RF]
theorem existsEtaleSquareAt_iff_existsOpenEtaleLocal {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}} [IsEtaleLocalAtSourceAndTarget P]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) :
    existsEtaleSquareAt (representedBy P) f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
          etaleLocal P (i ≫ f) :=
  sorry

/-- Lemma 67.22.7 (3): let `P` be étale local on source-and-target for scheme
morphisms, and let `Q` be the associated germ-morphism property
`representedBy P`. A morphism `f : X ⟶ Y` of algebraic spaces has
`etaleLocal P` if and only if `f` has `Q` at every point of `|X|`. -/
@[stacks 04RF]
theorem etaleLocal_iff_forall_existsEtaleSquareAt {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}} [IsEtaleLocalAtSourceAndTarget P]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    etaleLocal P f ↔
      ∀ x : Points X, existsEtaleSquareAt (representedBy P) f x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
