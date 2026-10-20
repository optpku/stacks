module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FlatAtlas

/-!
# Final bootstrap of algebraic spaces

An fppf sheaf on schemes over `S` is an algebraic space under any of the six
quotient or flat-atlas criteria below. The locally injective and locally surjective
comparison from the quotient presheaf expresses `F = U / R` after fppf
sheafification, while preserving the Type `u` quotient-presheaf universe.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Theorem 80.10.1 (1). A flat locally finitely presented equivalence-relation groupoid in algebraic spaces has
an algebraic-space quotient: an fppf sheaf locally bijective to its quotient presheaf is
an algebraic space. -/
@[stacks 04S6] #check (AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace.of_groupoidAlgebraicSpace :
  ∀ {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    [IsEquivalenceRelation G.t G.s] [Flat G.s.left] [Flat G.t.left]
    [LocallyOfFinitePresentation G.s.left] [LocallyOfFinitePresentation G.t.left]
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (η : G.toPreRelation.quotientPresheaf ⟶ F)
    (hη_inj : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (hη_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η),
    IsAlgebraicSpace F)

/- Theorem 80.10.1 (2). A flat locally finitely presented equivalence-relation groupoid scheme has an
algebraic-space quotient: an fppf sheaf locally bijective to its quotient presheaf is
an algebraic space. -/
@[stacks 04S6] #check (AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace.of_groupoidScheme :
  ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsEquivalenceRelation G.t G.s] [AlgebraicGeometry.Flat G.s.left]
    [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left]
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (η : G.toPreRelation.quotientPresheaf ⟶ F)
    (hη_inj : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (hη_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η),
    IsAlgebraicSpace F)

/- Theorem 80.10.1 (3). An fppf sheaf admitting a morphism from an algebraic space that is representable by
algebraic spaces, surjective, flat, and locally of finite presentation is an algebraic space. -/
@[stacks 04S6] #check (AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace.of_flat_locallyOfFinitePresentation_surjective :
  ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] (a : X ⟶ F)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) a),
    IsAlgebraicSpace F)

/- Theorem 80.10.1 (4). An fppf sheaf admitting a morphism from a scheme that is representable by algebraic
spaces, surjective, flat, and locally of finite presentation is an algebraic space. -/
@[stacks 04S6] #check (AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace.of_scheme_flat_locallyOfFinitePresentation_surjective :
  ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) {U : Over S}
    (a : yoneda.obj U ⟶ F)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) a),
    IsAlgebraicSpace F)

/- Theorem 80.10.1 (5). An fppf sheaf with diagonal representable by algebraic spaces and a surjective, flat,
locally finitely presented morphism from an algebraic space is an algebraic space. -/
@[stacks 04S6] #check (AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace.of_diag_flat_locallyOfFinitePresentation_surjective :
  ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hΔ : representableByAlgebraicSpaces (Limits.diag F))
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] (a : X ⟶ F)
    (hP : (representableByAlgebraicSpaces.of_diag_isAlgebraicSpace hΔ a).has
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S))),
    IsAlgebraicSpace F)

/- Theorem 80.10.1 (6). An fppf sheaf with diagonal representable by schemes and a surjective, flat, locally
finitely presented morphism from a scheme is an algebraic space. -/
@[stacks 04S6] #check (AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace.of_schemeDiag_flat_locallyOfFinitePresentation_surjective :
  ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag F)) {U : Over S}
    (a : yoneda.obj U ⟶ F)
    (ha : (over (@AlgebraicGeometry.Surjective ⊓ @AlgebraicGeometry.Flat ⊓
        @AlgebraicGeometry.LocallyOfFinitePresentation :
          MorphismProperty Scheme.{u})).presheaf a),
    IsAlgebraicSpace F)

/- Isomorphism invariance. If two functors on schemes over a base are isomorphic and the second is an algebraic
space, then the first is an algebraic space. -/
#check (AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace.of_iso :
  ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    (e : F ≅ G) [IsAlgebraicSpace G],
    IsAlgebraicSpace F)

/- Theorem 80.10.1 (4), scheme-representable branch. An fppf sheaf admitting a morphism from a scheme that is representable by schemes,
surjective, flat, and locally of finite presentation is an algebraic space. -/
@[stacks 04S6] #check (AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace.of_scheme_representable_flat_locallyOfFinitePresentation_surjective :
  ∀ {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) {U : Over S}
    (a : yoneda.obj U ⟶ F)
    (ha : (over (@AlgebraicGeometry.Surjective ⊓ @AlgebraicGeometry.Flat ⊓
        @AlgebraicGeometry.LocallyOfFinitePresentation :
          MorphismProperty Scheme.{u})).presheaf a),
    IsAlgebraicSpace F)

end AlgebraicGeometry.AlgebraicSpace
