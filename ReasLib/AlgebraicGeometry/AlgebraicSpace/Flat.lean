/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Locality.Criteria
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.Flat

/-!
# Flat morphisms of algebraic spaces

The flatness class and its étale-square API are owned by `Morphism.Flat`.
Flatness is equivalent to pointwise flatness and can be tested after scheme
base change, on étale presentations, or on Zariski coverings.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces is flat at a point `x` of `X` if
some étale scheme square over `f` has top arrow flat at a point of `U` mapping
to `x`. -/
def FlatAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (u : U.left),
    (over (@AlgebraicGeometry.Etale)).presheaf a ∧
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        a ≫ f = ofOverMap h ≫ b ∧
          Points.map a (ofOver.pointsEquiv U u) = x ∧
            Scheme.Hom.flatAt h.left u

/-- Flatness at a point is the existence of an étale scheme presentation whose
top arrow is flat at a germ mapping to that point. -/
theorem flatAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) :
    FlatAt f x ↔
      ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
        (u : U.left),
        (over (@AlgebraicGeometry.Etale)).presheaf a ∧
          (over (@AlgebraicGeometry.Etale)).presheaf b ∧
            a ≫ f = ofOverMap h ≫ b ∧
              Points.map a (ofOver.pointsEquiv U u) = x ∧
                Scheme.Hom.flatAt h.left u :=
  Iff.rfl

/-- A morphism of schemes over `S`, viewed as a morphism of algebraic spaces, is
flat if and only if the underlying morphism of schemes is flat. -/
theorem flat_ofOverMap_iff {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V) :
    Flat (ofOverMap h) ↔ AlgebraicGeometry.Flat h.left :=
  sorry

namespace Flat

/-- Every base change of `f` along a morphism from a scheme is flat.
Stacks, Tag 03MM (3), `tex/spaces-morphisms.tex:5841–5842`. -/
abbrev baseChangeOnSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  Locality.Criteria.forallScheme (@Flat S) f

/-- Every base change of `f` along a morphism from an affine scheme is flat.
Stacks, Tag 03MM (4), `tex/spaces-morphisms.tex:5843–5844`. -/
abbrev baseChangeOnAffineSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  Locality.Criteria.forallAffine (@Flat S) f

/-- There is a surjective étale morphism from a scheme to `Y` along which the
base change of `f` is flat.
Stacks, Tag 03MM (5), `tex/spaces-morphisms.tex:5845–5846`. -/
abbrev existsSurjectiveEtaleTarget {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  Locality.Criteria.existsSurjectiveEtaleTarget (@Flat S) f

/-- There is a surjective étale morphism `φ` from a scheme to `X` such that
`φ ≫ f` is flat.
Stacks, Tag 03MM (6), `tex/spaces-morphisms.tex:5847–5849`. -/
abbrev existsSurjectiveEtaleSource {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  Locality.Criteria.existsSurjectiveEtaleSource (@Flat S) f

/-- Every étale scheme square over `f` has flat top arrow.
Stacks, Tag 03MM (7), `tex/spaces-morphisms.tex:5850–5858`. -/
abbrev forallEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  Locality.Criteria.forallEtaleSquare (@AlgebraicGeometry.Flat) f

/-- There is an étale scheme square over `f` with surjective source cover and
flat top arrow.
Stacks, Tag 03MM (8), `tex/spaces-morphisms.tex:5859–5867`. -/
abbrev existsEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  Locality.Criteria.existsEtaleSquare (@AlgebraicGeometry.Flat) f

/-- There are Zariski coverings of `Y` and of the inverse images in `X` on which
the pieces of `f` are flat.
Stacks, Tag 03MM (9), `tex/spaces-morphisms.tex:5868–5870`. -/
abbrev existsZariskiCover {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  Locality.Criteria.existsZariskiCover.{u, v} (@Flat S) f

end Flat

/-- Flatness of a morphism of algebraic spaces is equivalent to pointwise
flatness, flatness after every scheme or affine-scheme base change, flatness
on a surjective étale target or source presentation, the universal or
existential étale scheme-square condition, and flatness on Zariski coverings
of the target and its inverse images.
Stacks, Tag 03MM, `tex/spaces-morphisms.tex:5834–5876`. -/
theorem flat_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    List.TFAE
      [ Flat f
      , ∀ x : Points X, FlatAt f x
      , Flat.baseChangeOnSchemes f
      , Flat.baseChangeOnAffineSchemes f
      , Flat.existsSurjectiveEtaleTarget f
      , Flat.existsSurjectiveEtaleSource f
      , Flat.forallEtaleSquare f
      , Flat.existsEtaleSquare f
      , Flat.existsZariskiCover.{u, v} f ] := by
  have hP : (@Flat S : MorphismProperty (AlgebraicSpace S)) =
      etaleLocal (@AlgebraicGeometry.Flat) := by
    funext U V g
    exact propext (flat_iff g)
  have hlocal := Locality.Criteria.etaleLocal_tfae.{u, v} (@AlgebraicGeometry.Flat) f
  have hbase : List.TFAE
      [ Flat f, Flat.baseChangeOnSchemes f, Flat.baseChangeOnAffineSchemes f
      , Flat.existsSurjectiveEtaleTarget f, Flat.existsSurjectiveEtaleSource f
      , Flat.forallEtaleSquare f, Flat.existsEtaleSquare f
      , Flat.existsZariskiCover.{u, v} f ] := by
    simpa only [Flat.baseChangeOnSchemes, Flat.baseChangeOnAffineSchemes,
      Flat.existsSurjectiveEtaleTarget, Flat.existsSurjectiveEtaleSource,
      Flat.forallEtaleSquare, Flat.existsEtaleSquare, Flat.existsZariskiCover, hP]
      using hlocal
  -- Tag 08EW, tex/spaces-morphisms.tex:5789–5810: the property-specific pointwise test.
  have hpoint : Flat f ↔ ∀ x : Points X, FlatAt f x := by sorry
  exact List.tfae_cons_cons.mpr ⟨hpoint,
    List.tfae_cons_cons.mpr ⟨hpoint.symm.trans (hbase.out 0 1),
      (List.tfae_cons_cons.mp hbase).2⟩⟩

/-- A morphism of algebraic spaces is flat if and only if it is flat at every
point of its source. -/
theorem flat_iff_forall_flatAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Flat f ↔ ∀ x : Points X, FlatAt f x :=
  (flat_tfae.{u, u} f).out 0 1

end AlgebraicGeometry.AlgebraicSpace
