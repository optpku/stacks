module

public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidualSpace
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Monomorphism
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat

/-!
# Existence of a monomorphic singleton over a point

For an algebraic stack `X` and a point `x : Points X`, the existence of a
monomorphism from a singleton algebraic stack whose image is `{x}` is equivalent
to the reduced version of that existence, and to the existence of a monomorphism
together with a surjective flat field-valued point sent to `x`. When these hold,
there is a unique strictly full subcategory of `X` that is a reduced locally
Noetherian singleton mapping to `x`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- There exists an algebraic stack `Z` and a monomorphism `f : Z ⟶ X` such that
`Points Z` is a singleton and `Set.range (Points.map f) = {x}`. -/
def existsMonoSingletonAt {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) : Prop :=
  ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (f : Z ⟶ X),
    Groupoids.Hom.Mono f ∧ Nonempty (Points Z) ∧ Subsingleton (Points Z) ∧
      Set.range (Points.map f) = {x}

namespace existsMonoSingletonAt

/-- `existsMonoSingletonAt X x` unpacks to a monomorphism from a singleton
algebraic stack whose image on points is `{x}`. -/
theorem iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} :
    existsMonoSingletonAt X x ↔
      ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (f : Z ⟶ X),
        Groupoids.Hom.Mono f ∧ Nonempty (Points Z) ∧ Subsingleton (Points Z) ∧
          Set.range (Points.map f) = {x} :=
  Iff.rfl

/-- A monomorphism from a singleton algebraic stack with image `{x}` witnesses
`existsMonoSingletonAt`. -/
theorem of {S : Scheme.{u}} {X Z : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Z] {x : Points X} (f : Z ⟶ X) [Groupoids.Hom.Mono f]
    [Nonempty (Points Z)] [Subsingleton (Points Z)]
    (hx : Set.range (Points.map f) = {x}) : existsMonoSingletonAt X x :=
  ⟨Z, inferInstance, f, inferInstance, inferInstance, inferInstance, hx⟩

/-- `existsMonoSingletonAt X x` supplies a monomorphism from a singleton
algebraic stack whose image on points is `{x}`. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (h : existsMonoSingletonAt X x) :
    ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (f : Z ⟶ X),
      Groupoids.Hom.Mono f ∧ Nonempty (Points Z) ∧ Subsingleton (Points Z) ∧
        Set.range (Points.map f) = {x} :=
  h

end existsMonoSingletonAt

/-- There exists a reduced algebraic stack `Z` and a monomorphism `f : Z ⟶ X`
such that `Points Z` is a singleton and `Set.range (Points.map f) = {x}`. -/
def existsReducedMonoSingletonAt {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) : Prop :=
  ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (f : Z ⟶ X),
    Groupoids.Hom.Mono f ∧ IsReduced Z ∧ Nonempty (Points Z) ∧
      Subsingleton (Points Z) ∧ Set.range (Points.map f) = {x}

namespace existsReducedMonoSingletonAt

/-- `existsReducedMonoSingletonAt X x` unpacks to a monomorphism from a reduced
singleton algebraic stack whose image on points is `{x}`. -/
theorem iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} :
    existsReducedMonoSingletonAt X x ↔
      ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (f : Z ⟶ X),
        Groupoids.Hom.Mono f ∧ IsReduced Z ∧ Nonempty (Points Z) ∧
          Subsingleton (Points Z) ∧ Set.range (Points.map f) = {x} :=
  Iff.rfl

/-- A monomorphism from a reduced singleton algebraic stack with image `{x}`
witnesses `existsReducedMonoSingletonAt`. -/
theorem of {S : Scheme.{u}} {X Z : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Z] [IsReduced Z] {x : Points X} (f : Z ⟶ X)
    [Groupoids.Hom.Mono f] [Nonempty (Points Z)] [Subsingleton (Points Z)]
    (hx : Set.range (Points.map f) = {x}) :
    existsReducedMonoSingletonAt X x :=
  ⟨Z, inferInstance, f, inferInstance, inferInstance, inferInstance, inferInstance, hx⟩

/-- `existsReducedMonoSingletonAt X x` supplies a monomorphism from a reduced
singleton algebraic stack whose image on points is `{x}`. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (h : existsReducedMonoSingletonAt X x) :
    ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (f : Z ⟶ X),
      Groupoids.Hom.Mono f ∧ IsReduced Z ∧ Nonempty (Points Z) ∧
        Subsingleton (Points Z) ∧ Set.range (Points.map f) = {x} :=
  h

end existsReducedMonoSingletonAt

/-- There exists an algebraic stack `Z`, a monomorphism `f : Z ⟶ X`, and a
field-valued point `p : FieldValuedPoint Z` whose morphism is surjective and
flat, such that `Points.map f (Points.mk p) = x`. -/
def existsMonoSurjectiveFlatSpecFieldAt {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) : Prop :=
  ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (f : Z ⟶ X)
    (p : FieldValuedPoint Z),
    Groupoids.Hom.Mono f ∧ Groupoids.Hom.Surjective p.hom ∧
      Groupoids.Hom.Flat p.hom ∧ Points.map f (Points.mk p) = x

namespace existsMonoSurjectiveFlatSpecFieldAt

/-- `existsMonoSurjectiveFlatSpecFieldAt X x` unpacks to a monomorphism
`f : Z ⟶ X` and a surjective flat field-valued point of `Z` sent to `x`. -/
theorem iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} :
    existsMonoSurjectiveFlatSpecFieldAt X x ↔
      ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (f : Z ⟶ X)
        (p : FieldValuedPoint Z),
        Groupoids.Hom.Mono f ∧ Groupoids.Hom.Surjective p.hom ∧
          Groupoids.Hom.Flat p.hom ∧ Points.map f (Points.mk p) = x :=
  Iff.rfl

/-- A monomorphism together with a surjective flat field-valued point sent to
`x` witnesses `existsMonoSurjectiveFlatSpecFieldAt`. -/
theorem of {S : Scheme.{u}} {X Z : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Z] {x : Points X} (f : Z ⟶ X) (p : FieldValuedPoint Z)
    [Groupoids.Hom.Mono f] [Groupoids.Hom.Surjective p.hom]
    [Groupoids.Hom.Flat p.hom] (hx : Points.map f (Points.mk p) = x) :
    existsMonoSurjectiveFlatSpecFieldAt X x :=
  ⟨Z, inferInstance, f, p, inferInstance, inferInstance, inferInstance, hx⟩

/-- `existsMonoSurjectiveFlatSpecFieldAt X x` supplies a monomorphism
`f : Z ⟶ X` and a surjective flat field-valued point of `Z` sent to `x`. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (h : existsMonoSurjectiveFlatSpecFieldAt X x) :
    ∃ (Z : GroupoidsOver S) (_ : AlgebraicStack Z) (f : Z ⟶ X)
      (p : FieldValuedPoint Z),
      Groupoids.Hom.Mono f ∧ Groupoids.Hom.Surjective p.hom ∧
        Groupoids.Hom.Flat p.hom ∧ Points.map f (Points.mk p) = x :=
  h

end existsMonoSurjectiveFlatSpecFieldAt

/-- A monomorphic singleton over a point exists exactly when a reduced one exists,
and exactly when a monomorphism admits a surjective flat field-valued point
mapping to that point. -/
theorem existsMonoSingletonAt_tfae {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) :
    List.TFAE
      [ existsMonoSingletonAt X x
      , existsReducedMonoSingletonAt X x
      , existsMonoSurjectiveFlatSpecFieldAt X x ] :=
  sorry

/-- Existence of a monomorphic singleton over `x` is equivalent to existence of
a reduced monomorphic singleton over `x`. -/
theorem existsMonoSingletonAt_iff_existsReducedMonoSingletonAt {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {x : Points X} :
    existsMonoSingletonAt X x ↔ existsReducedMonoSingletonAt X x :=
  (existsMonoSingletonAt_tfae X x).out 0 1

/-- Existence of a monomorphic singleton over `x` is equivalent to existence of
a monomorphism together with a surjective flat field-valued point sent to `x`. -/
theorem existsMonoSingletonAt_iff_existsMonoSurjectiveFlatSpecFieldAt
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {x : Points X} :
    existsMonoSingletonAt X x ↔ existsMonoSurjectiveFlatSpecFieldAt X x :=
  (existsMonoSingletonAt_tfae X x).out 0 2

/-- Existence of a reduced monomorphic singleton over `x` is equivalent to
existence of a monomorphism together with a surjective flat field-valued point
sent to `x`. -/
theorem existsReducedMonoSingletonAt_iff_existsMonoSurjectiveFlatSpecFieldAt
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {x : Points X} :
    existsReducedMonoSingletonAt X x ↔
      existsMonoSurjectiveFlatSpecFieldAt X x :=
  (existsMonoSingletonAt_tfae X x).out 1 2

/-- If a monomorphic singleton exists over a point, there is a unique replete
full subcategory whose restricted stack is reduced and locally Noetherian,
with singleton points mapping to that point. -/
theorem existsUnique_locallyNoetherian_strictlyFull_at {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X)
    (h : existsMonoSingletonAt X x) :
    ∃ (P : ObjectProperty X.total)
      (h_fibered : Functor.IsFibered.InGroupoids (P.ι ⋙ X.p))
      (h_algebraicStack : AlgebraicStack (Substack.category X P h_fibered))
      (h_reduced : IsReduced (Substack.category X P h_fibered))
      (h_locallyNoetherian : IsLocallyNoetherian (Substack.category X P h_fibered))
      (h_nonempty : Nonempty (Points (Substack.category X P h_fibered)))
      (h_subsingleton : Subsingleton (Points (Substack.category X P h_fibered)))
      (h_strictlyFull : P.IsClosedUnderIsomorphisms)
      (h_image : Set.range (Points.map (Substack.inclusion X P h_fibered)) = {x}),
      ∀ (Q : ObjectProperty X.total)
        (hQ_fibered : Functor.IsFibered.InGroupoids (Q.ι ⋙ X.p))
        (hQ_algebraicStack : AlgebraicStack (Substack.category X Q hQ_fibered))
        (hQ_reduced : IsReduced (Substack.category X Q hQ_fibered))
        (hQ_locallyNoetherian : IsLocallyNoetherian (Substack.category X Q hQ_fibered))
        (hQ_nonempty : Nonempty (Points (Substack.category X Q hQ_fibered)))
        (hQ_subsingleton : Subsingleton (Points (Substack.category X Q hQ_fibered)))
        (hQ_strictlyFull : Q.IsClosedUnderIsomorphisms)
        (hQ_image : Set.range (Points.map (Substack.inclusion X Q hQ_fibered)) = {x}),
        Q = P :=
  sorry

/-- Any two monomorphisms from reduced locally Noetherian singleton
algebraic stacks into `X` whose images on points are `{x}` have the same
essential image. -/
theorem unique_locallyNoetherian_strictlyFull_at {S : Scheme.{u}}
    {X Z Z' : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Z]
    [AlgebraicStack Z'] {x : Points X} (ι : Z ⟶ X) (ι' : Z' ⟶ X)
    [Groupoids.Hom.Mono ι] [Groupoids.Hom.Mono ι']
    [IsReduced Z] [IsReduced Z']
    [IsLocallyNoetherian Z] [IsLocallyNoetherian Z']
    [Nonempty (Points Z)] [Nonempty (Points Z')]
    [Subsingleton (Points Z)] [Subsingleton (Points Z')]
    (hι : Set.range (Points.map ι) = {x})
    (hι' : Set.range (Points.map ι') = {x}) :
    (toFunctor ι).essImage = (toFunctor ι').essImage :=
  sorry

/-- A monomorphism `ι : Z ⟶ X` of algebraic stacks is a residual gerbe of `X` at
`x` when `Z` is reduced, locally Noetherian, and a singleton, and the image of
`Points.map ι` is `{x}`. -/
class IsResidualGerbe {S : Scheme.{u}} {X Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] (ι : Z ⟶ X) (x : Points X) : Prop where
  /-- A residual-gerbe morphism is a monomorphism of groupoid fibrations. -/
  [mono : Groupoids.Hom.Mono ι]
  /-- The residual gerbe is reduced. -/
  [isReduced : IsReduced Z]
  /-- The residual gerbe is locally Noetherian. -/
  [isLocallyNoetherian : IsLocallyNoetherian Z]
  /-- The residual gerbe is a singleton. -/
  [subsingleton_points : Subsingleton (Points Z)]
  /-- The image of `Points.map ι` is the singleton `{x}`. -/
  image_eq : Set.range (Points.map ι) = {x}

namespace IsResidualGerbe

/-- The identity of a reduced, locally Noetherian singleton algebraic stack is a
residual gerbe at its unique point. -/
instance id {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
    [IsReduced Z] [IsLocallyNoetherian Z] [Subsingleton (Points Z)]
    {x : Points Z} : IsResidualGerbe (𝟙 Z) x :=
  sorry

/-- A residual-gerbe monomorphism is a monomorphism from a reduced, locally
Noetherian singleton algebraic stack whose image on points is `{x}`. -/
theorem spec {S : Scheme.{u}} {X Z : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Z] {ι : Z ⟶ X} {x : Points X} [IsResidualGerbe ι x] :
    Groupoids.Hom.Mono ι ∧ IsReduced Z ∧ IsLocallyNoetherian Z ∧
      Subsingleton (Points Z) ∧ Set.range (Points.map ι) = {x} :=
  ⟨IsResidualGerbe.mono (ι := ι) (x := x),
    IsResidualGerbe.isReduced (ι := ι) (x := x),
    IsResidualGerbe.isLocallyNoetherian (ι := ι) (x := x),
    IsResidualGerbe.subsingleton_points (ι := ι) (x := x),
    IsResidualGerbe.image_eq (ι := ι) (x := x)⟩

/-- A morphism of algebraic stacks is a residual gerbe at `x` if and only if it
is a monomorphism from a reduced, locally Noetherian singleton whose image on
points is `{x}`. -/
theorem iff {S : Scheme.{u}} {X Z : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Z] (ι : Z ⟶ X) (x : Points X) :
    IsResidualGerbe ι x ↔
      Groupoids.Hom.Mono ι ∧ IsReduced Z ∧ IsLocallyNoetherian Z ∧
        Subsingleton (Points Z) ∧ Set.range (Points.map ι) = {x} :=
  ⟨fun h => ⟨h.mono, h.isReduced, h.isLocallyNoetherian,
      h.subsingleton_points, h.image_eq⟩,
    fun ⟨hm, hr, hn, hs, hi⟩ =>
      { mono := hm
        isReduced := hr
        isLocallyNoetherian := hn
        subsingleton_points := hs
        image_eq := hi }⟩

/-- Every point of a residual gerbe maps to the marked point of the target. -/
theorem map_eq {S : Scheme.{u}} {X Z : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Z] {ι : Z ⟶ X} {x : Points X} [IsResidualGerbe ι x]
    (z : Points Z) : Points.map ι z = x :=
  sorry

/-- The image of a residual-space monomorphism of algebraic spaces is a residual
gerbe of the associated algebraic stacks. -/
theorem ofResidualSpace {S : Scheme.{u}} {X Z : AlgebraicSpace S} {ι : Z ⟶ X}
    (x : AlgebraicSpace.Points X) [AlgebraicSpace.IsResidualSpace ι x]
    (z : Points Z.toGroupoids) :
    IsResidualGerbe (AlgebraicSpace.toGroupoids.map ι)
      (Points.map (AlgebraicSpace.toGroupoids.map ι) z) :=
  sorry

end IsResidualGerbe

/-- The residue-field inclusion `U.left.fromSpecResidueField u` as a 1-morphism
of slice algebraic stacks over `S`. -/
def residueFieldι {S : Scheme.{u}} {U : Over S} (u : U.left) :
    GroupoidsOver.slice (Over.mk (U.left.fromSpecResidueField u ≫ U.hom)) ⟶
      GroupoidsOver.slice U :=
  overMap (Over.homMk (U.left.fromSpecResidueField u))

/-- `residueFieldι u` is `overMap` of `Over.homMk` of the residue-field map at
`u`. -/
theorem residueFieldι_eq {S : Scheme.{u}} {U : Over S} (u : U.left) :
    residueFieldι u = overMap (Over.homMk (U.left.fromSpecResidueField u)) :=
  rfl

/-- The point of `GroupoidsOver.slice U` represented by the residue-field
inclusion at `u`. -/
def residueFieldPoint {S : Scheme.{u}} {U : Over S} (u : U.left) :
    Points (GroupoidsOver.slice U) :=
  Points.mk
    (FieldValuedPoint.of (U.left.residueField u)
      (U.left.fromSpecResidueField u ≫ U.hom) (residueFieldι u))

/-- `residueFieldPoint u` is the class of the field-valued point given by
`residueFieldι u`. -/
theorem residueFieldPoint_eq {S : Scheme.{u}} {U : Over S} (u : U.left) :
    residueFieldPoint u =
      Points.mk
        (FieldValuedPoint.of (U.left.residueField u)
          (U.left.fromSpecResidueField u ≫ U.hom) (residueFieldι u)) :=
  rfl

/-- The canonical residue-field inclusion of a scheme point is its residual gerbe. -/
@[stacks 0H21]
instance isResidualGerbe_residueFieldι {S : Scheme.{u}} {U : Over S}
    (u : U.left) : IsResidualGerbe (residueFieldι u) (residueFieldPoint u) :=
  sorry

/-- An algebraic stack has a residual gerbe at a point when a monomorphism
from a singleton algebraic stack has that point as its image. -/
@[mk_iff]
class HasResidualGerbe {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    (x : Points X) : Prop where
  /-- There is a monomorphism from a singleton algebraic stack whose image on
  points is `{x}`. -/
  exists_mono_singleton : existsMonoSingletonAt X x

namespace HasResidualGerbe

/-- Existence of a residual gerbe supplies a monomorphism from a singleton
algebraic stack with the prescribed image on points. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} [HasResidualGerbe X x] : existsMonoSingletonAt X x :=
  HasResidualGerbe.exists_mono_singleton

/-- A residual gerbe exists exactly when a monomorphic singleton exists over
the marked point. -/
theorem iff_existsMonoSingletonAt {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} :
    HasResidualGerbe X x ↔ existsMonoSingletonAt X x :=
  ⟨fun h => h.exists_mono_singleton, fun h => ⟨h⟩⟩

/-- A residual gerbe exists exactly when a reduced monomorphic singleton
exists over the marked point. -/
theorem iff_existsReducedMonoSingletonAt {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} :
    HasResidualGerbe X x ↔ existsReducedMonoSingletonAt X x :=
  iff_existsMonoSingletonAt.trans
    existsMonoSingletonAt_iff_existsReducedMonoSingletonAt

/-- A residual gerbe exists exactly when a monomorphism admits a surjective
flat field-valued point mapping to the marked point. -/
theorem iff_existsMonoSurjectiveFlatSpecFieldAt {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {x : Points X} :
    HasResidualGerbe X x ↔ existsMonoSurjectiveFlatSpecFieldAt X x :=
  iff_existsMonoSingletonAt.trans
    existsMonoSingletonAt_iff_existsMonoSurjectiveFlatSpecFieldAt

/-- A monomorphism from a singleton algebraic stack with image `{x}` witnesses
existence of a residual gerbe at `x`. -/
theorem of_mono {S : Scheme.{u}} {X Z : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Z] {x : Points X} (f : Z ⟶ X) [Groupoids.Hom.Mono f]
    [Nonempty (Points Z)] [Subsingleton (Points Z)]
    (hx : Set.range (Points.map f) = {x}) : HasResidualGerbe X x :=
  ⟨existsMonoSingletonAt.of f hx⟩

end HasResidualGerbe

/-- A nonempty singleton algebraic stack has a residual gerbe at each point. -/
instance instHasResidualGerbe_of_subsingleton_points {S : Scheme.{u}}
    (Z : GroupoidsOver S) [AlgebraicStack Z] [Nonempty (Points Z)]
    [Subsingleton (Points Z)] {x : Points Z} : HasResidualGerbe Z x where
  exists_mono_singleton := existsMonoSingletonAt.of (𝟙 Z) sorry

/-- An object belongs to the residual-gerbe subcategory at `x` when it belongs
to a replete full subcategory whose inclusion is a residual gerbe at `x`. -/
def residualGerbeObjectProperty {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X)
    [HasResidualGerbe X x] : ObjectProperty X.total :=
  fun a => ∃ (Q : ObjectProperty X.total)
    (hf : Functor.IsFibered.InGroupoids (Q.ι ⋙ X.p))
    (ha : AlgebraicStack (Substack.category X Q hf)),
    Q.IsClosedUnderIsomorphisms ∧ IsResidualGerbe (Substack.inclusion X Q hf) x ∧ Q a

/-- Membership in the residual-gerbe subcategory is membership in some replete
full subcategory whose inclusion is a residual gerbe at the marked point. -/
theorem residualGerbeObjectProperty_mem_iff {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X)
    [HasResidualGerbe X x] (a : X.total) :
    residualGerbeObjectProperty X x a ↔
      ∃ (Q : ObjectProperty X.total)
        (hf : Functor.IsFibered.InGroupoids (Q.ι ⋙ X.p))
        (ha : AlgebraicStack (Substack.category X Q hf)),
        Q.IsClosedUnderIsomorphisms ∧
          IsResidualGerbe (Substack.inclusion X Q hf) x ∧ Q a :=
  Iff.rfl

/-- The projection of the residual-gerbe subcategory is fibred in groupoids. -/
instance instIsFiberedInGroupoids_residualGerbeObjectProperty
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X)
    [HasResidualGerbe X x] :
    Functor.IsFibered.InGroupoids
      ((residualGerbeObjectProperty X x).ι ⋙ X.p) :=
  sorry

/-- The residual gerbe at a point is the groupoid fibration restricted to its
residual-gerbe object property. -/
abbrev residualGerbe {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    (x : Points X) [HasResidualGerbe X x] : GroupoidsOver S :=
  Substack.category X (residualGerbeObjectProperty X x)
    (instIsFiberedInGroupoids_residualGerbeObjectProperty X x)

/-- The canonical inclusion of the residual-gerbe subcategory into the
ambient stack. -/
abbrev residualGerbeι {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    (x : Points X) [HasResidualGerbe X x] : residualGerbe X x ⟶ X :=
  Substack.inclusion X (residualGerbeObjectProperty X x)
    (instIsFiberedInGroupoids_residualGerbeObjectProperty X x)

/-- The residual gerbe is an algebraic stack. -/
instance instAlgebraicStack_residualGerbe {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) [HasResidualGerbe X x] :
    AlgebraicStack (residualGerbe X x) :=
  sorry

/-- The residual gerbe is reduced. -/
instance instIsReduced_residualGerbe {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) [HasResidualGerbe X x] :
    IsReduced (residualGerbe X x) :=
  sorry

/-- The residual gerbe is locally Noetherian. -/
instance instIsLocallyNoetherian_residualGerbe {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X)
    [HasResidualGerbe X x] : IsLocallyNoetherian (residualGerbe X x) :=
  sorry

/-- The point space of the residual gerbe is nonempty. -/
instance instNonempty_points_residualGerbe {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X)
    [HasResidualGerbe X x] : Nonempty (Points (residualGerbe X x)) :=
  sorry

/-- The point space of the residual gerbe is a subsingleton. -/
instance instSubsingleton_points_residualGerbe {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X)
    [HasResidualGerbe X x] : Subsingleton (Points (residualGerbe X x)) :=
  sorry

/-- The canonical residual-gerbe inclusion is a monomorphism. -/
instance instMono_residualGerbeι {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) [HasResidualGerbe X x] :
    Groupoids.Hom.Mono (residualGerbeι X x) :=
  sorry

/-- The canonical inclusion is a residual gerbe at the marked point. -/
instance instIsResidualGerbe_residualGerbeι {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X)
    [HasResidualGerbe X x] : IsResidualGerbe (residualGerbeι X x) x :=
  sorry

/-- The residual gerbe is a replete full reduced locally Noetherian singleton
algebraic substack, with monomorphic inclusion and point-image `{x}`. -/
theorem residualGerbe_properties {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) [HasResidualGerbe X x] :
    AlgebraicStack (residualGerbe X x) ∧ IsReduced (residualGerbe X x) ∧
      IsLocallyNoetherian (residualGerbe X x) ∧
      Nonempty (Points (residualGerbe X x)) ∧
      Subsingleton (Points (residualGerbe X x)) ∧
      (residualGerbeObjectProperty X x).IsClosedUnderIsomorphisms ∧
      (toFunctor (residualGerbeι X x)).Full ∧
      (toFunctor (residualGerbeι X x)).Faithful ∧
      Groupoids.Hom.Mono (residualGerbeι X x) ∧
      Set.range (Points.map (residualGerbeι X x)) = {x} :=
  sorry

/-- Any fully faithful inclusion of a reduced locally Noetherian singleton
algebraic stack with point-image `{x}` has the same essential image as the
canonical residual-gerbe inclusion. -/
theorem residualGerbe_essImage_unique {S : Scheme.{u}}
    {X Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Z] {x : Points X}
    [HasResidualGerbe X x] (ι : Z ⟶ X)
    (hι_full : (toFunctor ι).Full ∧ (toFunctor ι).Faithful) [IsReduced Z]
    [IsLocallyNoetherian Z] [Nonempty (Points Z)] [Subsingleton (Points Z)]
    (hι : Set.range (Points.map ι) = {x}) :
    (toFunctor ι).essImage = (toFunctor (residualGerbeι X x)).essImage :=
  sorry

end AlgebraicGeometry.AlgebraicStack
