/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap78.Lemma_78_17_1_Restriction

/-!
# Restriction comparison for morphisms of groupoids in algebraic spaces

A morphism `f : Hom G H` of groupoids in algebraic spaces induces a canonical
comparison from the arrow space of `G` into the restriction of `H` along `f.obj`.
The source phrase "`R` is the restriction of `R'` via `f : U ⟶ U'`" is the
predicate that this comparison is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.Hom

/-- A morphism of groupoids in algebraic spaces is compatible with the maps
`(t, s)` to the products of object spaces. -/
theorem restrictionArrow_w {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) :
    f.arrow ≫ H.toPreRelation.hom =
      G.toPreRelation.hom ≫ prod.map f.obj f.obj := sorry

/-- The canonical comparison from the arrow space of `G` to the arrow space of
the restriction of `H` along `f.obj`. -/
def restrictionArrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) :
    G.R ⟶ (H.pullback f.obj).R :=
  Limits.pullback.lift f.arrow G.toPreRelation.hom (restrictionArrow_w f)

/-- The comparison to the restricted arrow space recovers the original arrow map
after composing with the pullback projection. -/
theorem restrictionArrow_comp_pullbackArrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) :
    f.restrictionArrow ≫ pullbackArrow H f.obj = f.arrow := sorry

/-- The comparison to the restricted arrow space recovers the original map
`(t, s)`. -/
theorem restrictionArrow_comp_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) :
    f.restrictionArrow ≫ (H.pullback f.obj).toPreRelation.hom =
      G.toPreRelation.hom := sorry

/-- A morphism of groupoids in algebraic spaces exhibits the source arrow space
as the restriction of the target arrow space along the object map. -/
def IsRestriction {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) : Prop :=
  IsIso f.restrictionArrow

/-- The restriction predicate is the assertion that the canonical comparison of
arrow spaces is an isomorphism. -/
theorem isRestriction_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) :
    IsRestriction f ↔ IsIso f.restrictionArrow := sorry

/-- The restriction predicate is equivalent to the square of `(t, s)` along
`f.obj` being a pullback, recovering `R ≅ (U ⨯_B U) ×_{U' ⨯_B U'} R'`. -/
theorem isRestriction_iff_isPullback {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) :
    IsRestriction f ↔
      Nonempty
        (IsPullback f.arrow G.toPreRelation.hom H.toPreRelation.hom
          (prod.map f.obj f.obj)) := sorry

/-- The canonical restriction morphism of a groupoid along a map to its object
space exhibits the restricted arrow space as a restriction. -/
theorem pullbackHom_isRestriction {S : Scheme.{u}} {B : AlgebraicSpace S}
    (H : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ H.U) :
    IsRestriction (pullbackHom H g) := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.Hom
