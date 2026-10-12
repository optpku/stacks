/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_13_1_SchematicLocus
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Lemma_67_23_3_Pullback
public import stacks_project.Chap67.Lemma_67_23_6_Cancellation
public import stacks_project.Chap67.Lemma_67_38_5_Unramified

/-!
# Unramified source locus of a morphism of algebraic spaces

The largest open subspace of the source on which a morphism of algebraic spaces
is unramified, constructed as the subfunctor of maps whose image of points lands
in the pointwise unramified locus.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Unramified

/-- The subfunctor of maps into `X` whose image of points lands in the unramified
locus of `f`. -/
def sourceLocusSubfunctor {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Subfunctor X.functorOfPoints where
  obj U := {φ | Set.range (Points.map (ofYonedaSection φ)) ⊆ {x | UnramifiedAt f x}}
  map := sorry

/-- The algebraic space underlying the unramified source locus of `f`. -/
def sourceLocusSpace {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    AlgebraicSpace S :=
  ofFunctor (sourceLocusSubfunctor f).toFunctor sorry sorry sorry

/-- The inclusion of the unramified source locus of `f` into `X`. -/
def sourceLocusι {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    sourceLocusSpace f ⟶ X :=
  (sourceLocusSubfunctor f).ι

/-- The inclusion of the unramified source locus is an open immersion. -/
instance instIsOpenImmersion_sourceLocusι {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : IsOpenImmersion (sourceLocusι f) :=
  sorry

/-- The largest open subspace of `X` on which `f` is unramified. -/
def sourceLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    OpenSubspace X :=
  OpenSubspace.ofι (sourceLocusι f)

/-- The inclusion of `sourceLocus f` is an open immersion. -/
instance instIsOpenImmersion_sourceLocus_ι {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : IsOpenImmersion (sourceLocus f).ι :=
  (sourceLocus f).isOpenImmersion

/-- The restriction of `f` to its unramified source locus is unramified. -/
instance instUnramified_sourceLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Unramified ((sourceLocus f).ι ≫ f) :=
  sorry

/-- A point of `X` lies in the unramified source locus of `f` if and only if `f`
is unramified at that point. -/
theorem mem_sourceLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) :
    x ∈ (sourceLocus f).pointsSet ↔ UnramifiedAt f x :=
  sorry

/-- The points of the unramified source locus of `f` are exactly the points at
which `f` is unramified. -/
theorem sourceLocus_pointsSet_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (sourceLocus f).pointsSet = {x | UnramifiedAt f x} :=
  sorry

/-- Any open immersion along which `f` is unramified factors through the
unramified source locus on points. -/
theorem sourceLocus_maximal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {U : AlgebraicSpace S} (i : U ⟶ X) [IsOpenImmersion i]
    (hf : Unramified (i ≫ f)) :
    Set.range (Points.map i) ⊆ (sourceLocus f).pointsSet :=
  sorry

/-- The unramified source locus is the open subspace cut out by the pointwise
unramified subfunctor, included by an open immersion along which `f` is
unramified, whose points are exactly the points at which `f` is unramified. -/
theorem sourceLocus_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (sourceLocusSpace f).functorOfPoints =
        (sourceLocusSubfunctor f).toFunctor ∧
      sourceLocusι f = (sourceLocusSubfunctor f).ι ∧
      IsOpenImmersion (sourceLocusι f) ∧
      Unramified ((sourceLocus f).ι ≫ f) ∧
      ∀ x : Points X, x ∈ (sourceLocus f).pointsSet ↔ UnramifiedAt f x :=
  sorry

/-- The set of points at which `f` is unramified is open in `Points X`. -/
theorem isOpen_unramifiedAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : IsOpen (setOf (UnramifiedAt f)) :=
  sorry

/-- The cospan identity `(f ≫ q) ≫ 𝟙 Z = f ≫ q` used to induce
`overBaseChange`. -/
theorem overBaseChange_map_eq₁ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) : (f ≫ q) ≫ 𝟙 Z = f ≫ q :=
  sorry

/-- The identity-leg identity `g ≫ 𝟙 Z = 𝟙 Z' ≫ g` used to induce
`overBaseChange`. -/
theorem overBaseChange_map_eq₂ {S : Scheme.{u}} {Z Z' : AlgebraicSpace S}
    (g : Z' ⟶ Z) : g ≫ 𝟙 Z = 𝟙 Z' ≫ g :=
  sorry

/-- The base change of `f : X ⟶ Y` over `Z` along `g : Z' ⟶ Z`, as the
comparison `X ×_Z Z' ⟶ Y ×_Z Z'`. -/
def overBaseChange {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z) :
    pullback (f ≫ q) g ⟶ pullback q g :=
  pullback.map (f ≫ q) g q g f (𝟙 Z') (𝟙 Z)
    (overBaseChange_map_eq₁ f q) (overBaseChange_map_eq₂ g)

/-- The first projection identity for `overBaseChange`. -/
theorem overBaseChange_fst {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z) :
    overBaseChange f q g ≫ pullback.fst q g =
      pullback.fst (f ≫ q) g ≫ f :=
  sorry

/-- The second projection identity for `overBaseChange`. -/
theorem overBaseChange_snd {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z) :
    overBaseChange f q g ≫ pullback.snd q g =
      pullback.snd (f ≫ q) g :=
  sorry

/-- `overBaseChange` is the `pullback.map` comparison of `f` over `Z`, and it
commutes with both projections. -/
theorem overBaseChange_spec {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z) :
    overBaseChange f q g =
        pullback.map (f ≫ q) g q g f (𝟙 Z') (𝟙 Z)
          (overBaseChange_map_eq₁ f q) (overBaseChange_map_eq₂ g) ∧
      overBaseChange f q g ≫ pullback.fst q g =
        pullback.fst (f ≫ q) g ≫ f ∧
      overBaseChange f q g ≫ pullback.snd q g =
        pullback.snd (f ≫ q) g :=
  sorry

/-- In a cartesian square of algebraic spaces, pointwise unramifiedness is
preserved and reflected when the original morphism is locally of finite type. -/
theorem unramifiedAt_iff_of_isPullback {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hpb : IsPullback g' f' f g) [LocallyOfFiniteType f]
    (x' : Points X') :
    UnramifiedAt f' x' ↔ UnramifiedAt f (Points.map g' x') :=
  sorry

/-- In a cartesian square of algebraic spaces, the unramified source locus of the
base-changed morphism is the preimage of the original unramified source locus. -/
theorem sourceLocus_eq_preimage_of_isPullback {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hpb : IsPullback g' f' f g) [LocallyOfFiniteType f] :
    (sourceLocus f').pointsSet = Points.map g' ⁻¹' (sourceLocus f).pointsSet :=
  sorry

/-- In a cartesian square of algebraic spaces, the unramified source locus of the
base-changed morphism is the inverse image open of the original unramified
source locus. -/
theorem sourceLocus_eq_openInverseImage_of_isPullback {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hpb : IsPullback g' f' f g) [LocallyOfFiniteType f] :
    (sourceLocus f').pointsSet =
      Set.range (Points.map (openInverseImageι g' (sourceLocus f).ι)) :=
  sorry

/-- The unramified source locus of a canonical pullback projection is the
preimage of the unramified source locus along the other projection. -/
theorem sourceLocus_pullback_snd {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y' ⟶ Y) :
    (sourceLocus (pullback.snd f g)).pointsSet =
      Points.map (pullback.fst f g) ⁻¹' (sourceLocus f).pointsSet :=
  sorry

end Unramified

end AlgebraicGeometry.AlgebraicSpace
