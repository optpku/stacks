/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_18_1_Site

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous
public import stacks_project.Chap07.Definition_7_6_2_Site
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_18_3_Etale

/-!
# Small étale site and étale site of algebraic spaces

The small étale site of an algebraic space `X` has objects schemes étale over `X`. The
variant `X_spaces,étale` has objects algebraic spaces étale over `X`. The identity-on-objects
comparison is the comma functor from costructured arrows along `ofOver` into the étale slice
over `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- `ofOverFunctor S` is faithful. -/
instance ofOverFunctor_faithful (S : Scheme.{u}) : (ofOverFunctor S).Faithful :=
  sorry

/-- `ofOverFunctor S` is full. -/
instance ofOverFunctor_full (S : Scheme.{u}) : (ofOverFunctor S).Full :=
  sorry

/-- The small étale site of `X` is the costructured-arrow category of étale morphisms along
`ofOverFunctor`. -/
theorem smallEtaleSite_def {S : Scheme.{u}} (X : AlgebraicSpace S) :
    smallEtaleSite X =
      MorphismProperty.CostructuredArrow (@Etale S) ⊤ (ofOverFunctor S) X :=
  rfl

/-- The structural morphism of an object of the small étale site of `X` is étale. -/
instance etale_smallEtaleSite {S : Scheme.{u}} {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    Etale U.hom :=
  U.prop

/-- The structural morphism of an object of the small étale site is étale as a morphism from a
scheme to an algebraic space. -/
theorem isEtaleFromScheme_smallEtaleSite {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X) : isEtaleFromScheme U.hom :=
  sorry

/-- The underlying category of the étale site of algebraic spaces over `X`: objects are étale
morphisms of algebraic spaces into `X`. -/
abbrev spacesEtaleSite {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  MorphismProperty.Over (@Etale S) ⊤ X

/-- The étale site of algebraic spaces over `X` is the étale slice of `Over X`. -/
theorem spacesEtaleSite_def {S : Scheme.{u}} (X : AlgebraicSpace S) :
    spacesEtaleSite X = MorphismProperty.Over (@Etale S) ⊤ X :=
  rfl

/-- The structural morphism of an object of the étale site of algebraic spaces over `X` is
étale. -/
instance etale_spacesEtaleSite {S : Scheme.{u}} {X : AlgebraicSpace S} (U : spacesEtaleSite X) :
    Etale U.hom :=
  U.prop

/-- The identity-on-objects functor `X_étale ⥤ X_spaces,étale` sending a scheme étale over `X`
to the same object viewed as an algebraic space. -/
def smallEtaleInclusion {S : Scheme.{u}} (X : AlgebraicSpace S) :
    smallEtaleSite X ⥤ spacesEtaleSite X :=
  CostructuredArrow.toOver (@Etale S) (ofOverFunctor S) X

/-- `smallEtaleInclusion X` is the comma comparison `CostructuredArrow.toOver` along
`ofOverFunctor`. -/
theorem smallEtaleInclusion_def {S : Scheme.{u}} (X : AlgebraicSpace S) :
    smallEtaleInclusion X = CostructuredArrow.toOver (@Etale S) (ofOverFunctor S) X :=
  rfl

/-- On objects, `smallEtaleInclusion X` has the same structural morphism into `X`. -/
@[simp]
theorem smallEtaleInclusion_obj_hom {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : smallEtaleSite X) : ((smallEtaleInclusion X).obj U).hom = U.hom :=
  rfl

/-- On objects, `smallEtaleInclusion X` sends a scheme over `S` to the associated algebraic
space. -/
@[simp]
theorem smallEtaleInclusion_obj_left {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : smallEtaleSite X) : ((smallEtaleInclusion X).obj U).left = ofOver U.left :=
  rfl

/-- On morphisms, `smallEtaleInclusion X` applies `ofOverMap` to the underlying map of schemes. -/
@[simp]
theorem smallEtaleInclusion_map_left {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V : smallEtaleSite X} (f : U ⟶ V) :
    ((smallEtaleInclusion X).map f).left = ofOverMap f.left :=
  rfl

/-- A displayed family is a covering in the small étale precoverage of `X` if and only if the
underlying maps of schemes are jointly surjective. This is a characterization of the
canonical comap precoverage from Definition 66.18.1: morphisms between schemes étale over
`X` are themselves étale, so the remaining covering condition is joint surjectivity.
It does not redefine the precoverage or identify arbitrary presieves by presentation size. -/
theorem ofArrows_mem_smallEtalePrecoverage_iff_jointlySurjective {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : Type u} [Small.{u} I] {U : smallEtaleSite X} {V : I → smallEtaleSite X}
    {f : ∀ i, V i ⟶ U} :
    Presieve.ofArrows V f ∈ smallEtalePrecoverage X U ↔
      ⋃ i, Set.range (f i).left.left = Set.univ :=
  sorry

/-- The étale precoverage on algebraic spaces étale over `X`: covering presieves are those
presented by a small family whose induced maps on points are jointly surjective. -/
def spacesEtalePrecoverage {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Precoverage (spacesEtaleSite X) where
  coverings U :=
    { R | ∃ (I : Type u) (_ : Small.{u} I) (V : I → spacesEtaleSite X) (f : ∀ i, V i ⟶ U),
        R = Presieve.ofArrows V f ∧
          ⋃ i, Set.range (Points.map (f i).left) = Set.univ }

/-- A displayed family is a covering in the étale precoverage of algebraic spaces over `X` if and
only if `|U| = ⋃ i, (f i).left '' |V i|`. -/
theorem ofArrows_mem_spacesEtalePrecoverage_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : Type u} [Small.{u} I] {U : spacesEtaleSite X} {V : I → spacesEtaleSite X}
    {f : ∀ i, V i ⟶ U} :
    Presieve.ofArrows V f ∈ spacesEtalePrecoverage X U ↔
      ⋃ i, Set.range (Points.map (f i).left) = Set.univ :=
  sorry

/-- The étale topology of algebraic spaces over `X` is the Grothendieck topology generated by
jointly surjective families on points. -/
def spacesEtaleTopology {S : Scheme.{u}} (X : AlgebraicSpace S) :
    GrothendieckTopology (spacesEtaleSite X) :=
  (spacesEtalePrecoverage X).toGrothendieck

/-- The étale topology of algebraic spaces over `X` is generated by its spaces étale
precoverage. -/
theorem spacesEtaleTopology_def {S : Scheme.{u}} (X : AlgebraicSpace S) :
    spacesEtaleTopology X = (spacesEtalePrecoverage X).toGrothendieck :=
  rfl

/-- The étale covering families of algebraic spaces over `X` satisfy the site axioms. -/
instance spacesEtalePrecoverage.instIsSite {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (spacesEtalePrecoverage X).IsSite :=
  sorry

/-- The opposite of the small étale inclusion has pointwise right Kan extensions on sheaves of
types in universe `u + 1`. -/
instance smallEtaleInclusion_op_hasPointwiseRightKanExtension {S : Scheme.{u}}
    (X : AlgebraicSpace S) (P : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    (smallEtaleInclusion X).op.HasPointwiseRightKanExtension P :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
