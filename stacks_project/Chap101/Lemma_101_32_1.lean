module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.PreRelation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import stacks_project.Chap94.«94_8_2_1_FullyFaithful»
public import stacks_project.Chap94.Definition_94_16_5_Quotient

/-!
# Quotient of an open groupoid over a flat locally finitely presented atlas

If `(U, R, s, t, c)` is a groupoid in algebraic spaces over an algebraic space
`Y` with `U ⟶ Y` flat and locally of finite presentation and
`R ⟶ U ×_Y U` an open immersion, then `[U / R]` is an algebraic space and the
structure morphism to `Y` is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The morphism `U ⟶ X` recovered from the atlas `U ⟶ [U / R]` along a
presentation of the quotient stack by an algebraic space `X`. -/
def atlasSpace {S : Scheme.{u}} {Y : AlgebraicSpace S} (G : GroupoidAlgebraicSpace Y)
    {X : AlgebraicSpace S} (e : G.quotientStack ≌ X.toGroupoids) : G.U.left ⟶ X :=
  AlgebraicSpace.toGroupoids.recover (Bicategory.Equivalence.id _) e G.atlas

/-- `atlasSpace` is the algebraic-space morphism recovered from the atlas. -/
theorem atlasSpace_spec {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace Y) {X : AlgebraicSpace S}
    (e : G.quotientStack ≌ X.toGroupoids) :
    atlasSpace G e =
      AlgebraicSpace.toGroupoids.recover (Bicategory.Equivalence.id _) e G.atlas :=
  sorry

/-- The stack atlas induces `atlasSpace` relative to the identity presentation of
`U` and the given presentation of `[U / R]`. -/
theorem atlasSpace_inducesHom {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace Y) {X : AlgebraicSpace S}
    (e : G.quotientStack ≌ X.toGroupoids) :
    AlgebraicSpace.toGroupoids.InducesHom G.atlas (Bicategory.Equivalence.id _) e
      (atlasSpace G e) :=
  sorry

/-- Lemma 101.32.1 (1): let `Y` be an algebraic space. Let `(U, R, s, t, c)` be a
groupoid in algebraic spaces over `Y`. Assume `U ⟶ Y` is flat and locally of
finite presentation and `R ⟶ U ×_Y U` an open immersion. Then `X = [U / R] = U / R`
is an algebraic space. -/
@[stacks 0DU1]
theorem isRepresentableByAlgebraicSpace_quotientStack {S : Scheme.{u}}
    {Y : AlgebraicSpace S} (G : GroupoidAlgebraicSpace Y)
    [AlgebraicSpace.Flat G.U.hom]
    [AlgebraicSpace.LocallyOfFinitePresentation G.U.hom]
    [AlgebraicSpace.IsOpenImmersion G.toPreRelation.hom.left] :
    IsRepresentableByAlgebraicSpace G.quotientStack :=
  sorry

/-- Lemma 101.32.1 (2): under the same hypotheses, if `X` presents `[U / R]`, then
the structure morphism `X ⟶ Y` through which `U ⟶ Y` factors via the atlas is
étale. -/
@[stacks 0DU1]
theorem etale_of_atlas_comp {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace Y)
    [AlgebraicSpace.Flat G.U.hom]
    [AlgebraicSpace.LocallyOfFinitePresentation G.U.hom]
    [AlgebraicSpace.IsOpenImmersion G.toPreRelation.hom.left]
    {X : AlgebraicSpace S} (e : G.quotientStack ≌ X.toGroupoids)
    (f : X ⟶ Y) (hf : atlasSpace G e ≫ f = G.U.hom) :
    AlgebraicSpace.Etale f :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
