/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.EquivalenceRelation
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.GroupoidScheme
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientPresheaf
public import stacks_project.Chap65.Lemma_65_16_4_IsAlgebraicSpace
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap78.Definition_78_11_1_Groupoid
public import stacks_project.Chap78.Lemma_78_11_2_Groupoid
public import stacks_project.Chap78.«78_19_0_1_QuotientPresheaf»
public import stacks_project.Chap80.Definition_80_4_1_Relative
public import stacks_project.Chap80.Lemma_80_5_1

/-!
# Final bootstrap of algebraic spaces

An fppf sheaf on schemes over `S` is an algebraic space as soon as it arises as
the quotient `U / R` of a groupoid in algebraic spaces or of a groupoid scheme
with flat locally finitely presented source and target and equivalence relation
`j = (t, s)`, or as soon as it admits a surjective flat locally finitely
presented atlas from an algebraic space or a scheme, either representable by
algebraic spaces (or schemes), or with representable diagonal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Theorem 80.10.1 (1): let `S` be a scheme. If `(U, R, s, t, c)` is a groupoid
in algebraic spaces over `S` such that `s, t` are flat and locally of finite
presentation, and `j = prod.lift t s` is an equivalence relation, then
`F = U / R` is an algebraic space: any fppf sheaf `F` receiving a locally
bijective map from the Type `u` quotient presheaf of the underlying
pre-relation is an algebraic space. -/
@[stacks 04S6]
theorem IsAlgebraicSpace.of_groupoidAlgebraicSpace {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    [IsEquivalenceRelation G.t G.s] [Flat G.s.left] [Flat G.t.left]
    [LocallyOfFinitePresentation G.s.left] [LocallyOfFinitePresentation G.t.left]
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (η : G.toPreRelation.quotientPresheaf ⟶ F)
    (hη_inj : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (hη_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η) :
    IsAlgebraicSpace F :=
  sorry

/-- Theorem 80.10.1 (2): let `S` be a scheme. If `(U, R, s, t, c)` is a groupoid
scheme over `S` such that `s, t` are flat and locally of finite presentation,
and `j = prod.lift t s` is an equivalence relation, then `F = U / R` is an
algebraic space: any fppf sheaf `F` receiving a locally bijective map from the
Type `u` quotient presheaf of the underlying pre-relation is an algebraic
space. -/
@[stacks 04S6]
theorem IsAlgebraicSpace.of_groupoidScheme {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsEquivalenceRelation G.t G.s] [AlgebraicGeometry.Flat G.s.left]
    [AlgebraicGeometry.Flat G.t.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.s.left]
    [AlgebraicGeometry.LocallyOfFinitePresentation G.t.left]
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (η : G.toPreRelation.quotientPresheaf ⟶ F)
    (hη_inj : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (hη_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η) :
    IsAlgebraicSpace F :=
  sorry

/-- Theorem 80.10.1 (3): let `S` be a scheme. Let `F : (Over S)ᵒᵖ ⥤ Type u` be a
functor. If `F` is a sheaf for the fppf topology, and there is an algebraic
space `X` with a map `X ⟶ F` which is representable by algebraic spaces,
surjective, flat, and locally of finite presentation, then `F` is an algebraic
space. -/
@[stacks 04S6]
theorem IsAlgebraicSpace.of_flat_locallyOfFinitePresentation_surjective
    {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] (a : X ⟶ F)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) a) :
    IsAlgebraicSpace F :=
  sorry

/-- Theorem 80.10.1 (4): let `S` be a scheme. Let `F : (Over S)ᵒᵖ ⥤ Type u` be a
functor. If `F` is a sheaf for the fppf topology, and there is a scheme `U`
over `S` with a map `yoneda.obj U ⟶ F` which is representable by algebraic
spaces, surjective, flat, and locally of finite presentation, then `F` is an
algebraic space. -/
@[stacks 04S6]
theorem IsAlgebraicSpace.of_scheme_flat_locallyOfFinitePresentation_surjective
    {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) {U : Over S}
    (a : yoneda.obj U ⟶ F)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) a) :
    IsAlgebraicSpace F :=
  sorry

/-- Theorem 80.10.1 (5): let `S` be a scheme. Let `F : (Over S)ᵒᵖ ⥤ Type u` be a
functor. If `F` is a sheaf for the fppf topology, the diagonal `diag F` is
representable by algebraic spaces, and there is an algebraic space `X` with a
map `X ⟶ F` which is surjective, flat, and locally of finite presentation,
then `F` is an algebraic space. -/
@[stacks 04S6]
theorem IsAlgebraicSpace.of_diag_flat_locallyOfFinitePresentation_surjective
    {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hΔ : representableByAlgebraicSpaces (diag F))
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] (a : X ⟶ F)
    (hP : (representableByAlgebraicSpaces.of_diag_isAlgebraicSpace hΔ a).has
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S))) :
    IsAlgebraicSpace F :=
  sorry

/-- Theorem 80.10.1 (6): let `S` be a scheme. Let `F : (Over S)ᵒᵖ ⥤ Type u` be a
functor. If `F` is a sheaf for the fppf topology, the diagonal `diag F` is
representable by schemes, and there is a scheme `U` over `S` with a map
`yoneda.obj U ⟶ F` which is surjective, flat, and locally of finite
presentation, then `F` is an algebraic space. -/
@[stacks 04S6]
theorem IsAlgebraicSpace.of_schemeDiag_flat_locallyOfFinitePresentation_surjective
    {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hΔ : yoneda.relativelyRepresentable (diag F)) {U : Over S}
    (a : yoneda.obj U ⟶ F)
    (ha : (over (@AlgebraicGeometry.Surjective ⊓ @AlgebraicGeometry.Flat ⊓
        @AlgebraicGeometry.LocallyOfFinitePresentation :
          MorphismProperty Scheme.{u})).presheaf a) :
    IsAlgebraicSpace F :=
  sorry

/-- If `F ≅ G` as functors on `(Over S)ᵒᵖ` and `G` is an algebraic space, then
`F` is an algebraic space. -/
theorem IsAlgebraicSpace.of_iso {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    (e : F ≅ G) [IsAlgebraicSpace G] : IsAlgebraicSpace F :=
  sorry

/-- If `F` is an fppf sheaf and there is a scheme `U` over `S` with a morphism
`yoneda.obj U ⟶ F` which is representable by schemes, surjective, flat, and
locally of finite presentation, then `F` is an algebraic space. -/
theorem IsAlgebraicSpace.of_scheme_representable_flat_locallyOfFinitePresentation_surjective
    {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) {U : Over S}
    (a : yoneda.obj U ⟶ F)
    (ha : (over (@AlgebraicGeometry.Surjective ⊓ @AlgebraicGeometry.Flat ⊓
        @AlgebraicGeometry.LocallyOfFinitePresentation :
          MorphismProperty Scheme.{u})).presheaf a) :
    IsAlgebraicSpace F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
