/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.CategoryTheory.GradedObject.Single
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import ReasLib.AlgebraicGeometry.BivariantClass.Additive
public import ReasLib.AlgebraicGeometry.ChowMotive.Duality
public import ReasLib.AlgebraicGeometry.ChowMotive.Functor
public import ReasLib.AlgebraicGeometry.ChowMotive.Monoidal
public import ReasLib.AlgebraicGeometry.ChowMotive.Tate
public import ReasLib.AlgebraicGeometry.Correspondence.GradedCategory
public import ReasLib.AlgebraicGeometry.Correspondence.Chow
public import ReasLib.AlgebraicGeometry.Correspondence.Graph
public import ReasLib.AlgebraicGeometry.Correspondence.GraphEvaluation
public import ReasLib.AlgebraicGeometry.Correspondence.GradedCategory.Linear
public import ReasLib.CategoryTheory.GradedObject.Duality
public import ReasLib.CategoryTheory.GradedObject.Instances
public import ReasLib.CategoryTheory.GradedObject.KoszulBraiding
public import ReasLib.CategoryTheory.Idempotents.Karoubi.Linear
public import ReasLib.CategoryTheory.Monoidal.Duality.Functor

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped CategoryTheory.MonoidalCategory TensorProduct

noncomputable section

universe u v

namespace ChowMotive

open AlgebraicGeometry AlgebraicGeometry.Correspondence
open TopologicalSpace

variable {k : Type u} [Field k]

/-- Integral correspondences inherit the pointwise additive group of bivariant classes. -/
def integralAddCommGroup (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (r : ℤ) :
    AddCommGroup (Correspondence.Integral X Y r) :=
  BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) Limits.prod.snd r

/-- The canonical extension-of-scalars map from an integral correspondence to
the associated rational correspondence. -/
def toRational (X Y : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (r : ℤ)
    (alpha : Correspondence.Integral X Y r) :
    Correspondence.Rational X Y r :=
  BivariantClass.rationalize (fun _ ↦ 0) (Limits.prod.snd : X ⨯ Y ⟶ Y) r alpha

namespace Tate

/-- The point twist of index `-n` tensored with `h(X)(n)` maps canonically to
the untwisted motive `h(X)`. -/
theorem untwistHom_comm
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] (n : ℤ) :
    let f : (tateTwist (SchemeOverField.point k) (-n) ⊗ tateTwist X n).X ⟶ (h X).X :=
      Correspondence.GradedCategory.homOfDegreeZero (neg_add_cancel n)
        (Correspondence.rationalGraphIso _ _
          (Correspondence.GradedCategory.leftUnitorSchemeIso
            (Correspondence.GradedCategory.ofScheme X n)))
    (tateTwist (SchemeOverField.point k) (-n) ⊗ tateTwist X n).p ≫ f ≫
      (h X).p = f := sorry

/-- The canonical motivic map cancelling opposite Tate twists. -/
def untwistHom
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] (n : ℤ) :
    tateTwist (SchemeOverField.point k) (-n) ⊗ tateTwist X n ⟶ h X where
  f := Correspondence.GradedCategory.homOfDegreeZero (neg_add_cancel n)
    (Correspondence.rationalGraphIso _ _
      (Correspondence.GradedCategory.leftUnitorSchemeIso
        (Correspondence.GradedCategory.ofScheme X n)))
  comm := untwistHom_comm X n

/-- The underlying correspondence of `untwistHom` is the graph of the left unitor. -/
theorem untwistHom_f
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] (n : ℤ) :
    (untwistHom X n).f =
      (Correspondence.GradedCategory.homOfDegreeZero (neg_add_cancel n)
        (Correspondence.rationalGraphIso _ _
          (Correspondence.GradedCategory.leftUnitorSchemeIso
            (Correspondence.GradedCategory.ofScheme X n))) :
        (tateTwist (SchemeOverField.point k) (-n) ⊗ tateTwist X n).X ⟶
          (h X).X) := sorry

end Tate

/-- The diagonal multiplication has equal source and target Tate degree. -/
theorem diagonalMultiplication_degree
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] :
    (h X ⊗ h X).X.2 = (h X).X.2 := sorry

/-- The diagonal correspondence as the multiplication morphism of the motive of a smooth
projective scheme. -/
def diagonalMultiplication (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] :
    h X ⊗ h X ⟶ h X where
  f := GradedCategory.homOfDegreeZero (diagonalMultiplication_degree X)
    (Correspondence.rationalGraph (CategoryTheory.Limits.prod.lift (𝟙 X) (𝟙 X)))
  comm := sorry

/-- The underlying correspondence of motivic multiplication is the diagonal graph. -/
theorem diagonalMultiplication_f
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] :
    (diagonalMultiplication X).f =
      GradedCategory.homOfDegreeZero (diagonalMultiplication_degree X)
        (Correspondence.rationalGraph (CategoryTheory.Limits.prod.lift (𝟙 X) (𝟙 X))) := sorry

/-- The structure morphism of a smooth projective scheme, viewed contravariantly as
the unit morphism from the point motive to `h(X)`. -/
def unitMorphism (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] :
    𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) ⟶ h X where
  f := GradedCategory.homOfDegreeZero rfl
    (Correspondence.rationalGraph (CategoryTheory.Limits.terminal.from X))
  comm := sorry

/-- The underlying correspondence of the motivic unit is the graph of the structure
morphism `X ⟶ Spec(k)`. -/
theorem unitMorphism_f (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] :
    (unitMorphism X).f =
      (GradedCategory.homOfDegreeZero rfl
        (Correspondence.rationalGraph (CategoryTheory.Limits.terminal.from X)) :
        (𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k))).X ⟶
          (h X).X) := sorry

/-- The comparison from the tensor of two scheme motives to the motive of their
geometric product. -/
def productComparisonHom (X Y : Correspondence.Category k) :
    h X.scheme ⊗ h Y.scheme ⟶ h (Correspondence.Category.product X Y).scheme where
  f := GradedCategory.homOfDegreeZero rfl
    (Correspondence.rationalGraphIso _ _ (Iso.refl _))
  comm := sorry

/-- The inverse comparison from the motive of a geometric product to the tensor of
the two factor motives. -/
def productComparisonInv (X Y : Correspondence.Category k) :
    h (Correspondence.Category.product X Y).scheme ⟶ h X.scheme ⊗ h Y.scheme where
  f := GradedCategory.homOfDegreeZero rfl
    (Correspondence.rationalGraphIso _ _ (Iso.refl _))
  comm := sorry

/-- The tensor of two scheme motives is canonically isomorphic to the motive of their
geometric product. -/
def productComparisonIso (X Y : Correspondence.Category k) :
    h X.scheme ⊗ h Y.scheme ≅ h (Correspondence.Category.product X Y).scheme where
  hom := productComparisonHom X Y
  inv := productComparisonInv X Y
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of the product comparison is the identity graph on the underlying
geometric product. -/
theorem productComparisonIso_hom (X Y : Correspondence.Category k) :
    (productComparisonIso X Y).hom = productComparisonHom X Y := sorry

/-- The inverse map of the product comparison is the inverse identity graph. -/
theorem productComparisonIso_inv (X Y : Correspondence.Category k) :
    (productComparisonIso X Y).inv = productComparisonInv X Y := sorry

/-- The degree of a codimension-`r` cycle agrees with the Hom degree from the
`(-r)`-twisted point motive to `h(X)`. -/
theorem cycleMorphism_degree
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] (r : ℤ) :
    r = (h X).X.2 - (tateTwist (SchemeOverField.point k) (-r)).X.2 := sorry

/-- A codimension-`r` rational Chow correspondence from the point defines a morphism
from the `(-r)`-twisted Tate motive to `h(X)`. -/
def cycleMorphism (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    (r : ℤ) (alpha : Correspondence.Rational (SchemeOverField.point k) X r) :
    tateTwist (SchemeOverField.point k) (-r) ⟶ h X where
  f := Correspondence.castDegree (cycleMorphism_degree X r) alpha
  comm := sorry

/-- The underlying correspondence of `cycleMorphism` is the supplied cycle, after
the canonical degree transport. -/
theorem cycleMorphism_f (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    (r : ℤ) (alpha : Correspondence.Rational (SchemeOverField.point k) X r) :
    (cycleMorphism X r alpha).f =
      Correspondence.castDegree (cycleMorphism_degree X r) alpha := sorry

/-- The graph of a geometric morphism, viewed as the contravariant morphism of Chow
motives that induces cohomological pullback. -/
def pullbackMorphism {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [Smooth Y.hom] [Projective Y.hom]
    (f : X ⟶ Y) : h Y ⟶ h X where
  f := GradedCategory.homOfDegreeZero rfl (Correspondence.rationalGraph f)
  comm := sorry

/-- The graph of a geometric morphism between equally Tate-twisted motives. -/
def twistedPullbackMorphism {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [Smooth Y.hom] [Projective Y.hom]
    (f : X ⟶ Y) (n : ℤ) : tateTwist Y n ⟶ tateTwist X n where
  f := GradedCategory.homOfDegreeZero rfl (Correspondence.rationalGraph f)
  comm := sorry

/-- The underlying correspondence of twisted motivic pullback is the graph of the
geometric morphism. -/
theorem twistedPullbackMorphism_f {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [Smooth Y.hom] [Projective Y.hom]
    (f : X ⟶ Y) (n : ℤ) :
    (twistedPullbackMorphism f n).f =
      (GradedCategory.homOfDegreeZero rfl (Correspondence.rationalGraph f) :
        (tateTwist Y n).X ⟶ (tateTwist X n).X) := sorry

/-- The underlying correspondence of motivic pullback is the graph of the geometric
morphism. -/
theorem pullbackMorphism_f {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [Smooth Y.hom] [Projective Y.hom]
    (f : X ⟶ Y) :
    (pullbackMorphism f).f =
      (GradedCategory.homOfDegreeZero rfl (Correspondence.rationalGraph f) :
        (h Y).X ⟶ (h X).X) := sorry

/-- Pull a codimension-`r` rational Chow cycle back by composing it with the graph
correspondence. -/
def cyclePullback {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [Smooth Y.hom] [Projective Y.hom]
    (f : X ⟶ Y) (r : ℤ)
    (beta : Correspondence.Rational (SchemeOverField.point k) Y r) :
    Correspondence.Rational (SchemeOverField.point k) X r :=
  Correspondence.castDegree (add_zero r)
    (Correspondence.composition (SchemeOverField.point k) Y X r 0 beta
      (Correspondence.rationalGraph f))

/-- Motivic pullback of a cycle is composition with the graph correspondence. -/
theorem cyclePullback_def {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [Smooth Y.hom] [Projective Y.hom]
    (f : X ⟶ Y) (r : ℤ)
    (beta : Correspondence.Rational (SchemeOverField.point k) Y r) :
    cyclePullback f r beta =
      Correspondence.castDegree (add_zero r)
        (Correspondence.composition (SchemeOverField.point k) Y X r 0 beta
          (Correspondence.rationalGraph f)) := sorry

/-- The transposed graph of a morphism, with its dimension shift, gives the motivic
map that induces the Poincaré pushforward. -/
def pushforwardMorphism {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    [Smooth Y.hom] [Projective Y.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : X ⟶ Y) :
    h X ⟶ tateTwist Y ((e : ℤ) - d) where
  f := Correspondence.castDegree
    ((add_zero ((e : ℤ) - d)).trans (sub_zero ((e : ℤ) - d)).symm)
    (Correspondence.transpose Y X e d hYdim hXdim 0
      (Correspondence.rationalGraph f))
  comm := sorry

/-- The underlying Poincaré pushforward correspondence is the transposed graph. -/
theorem pushforwardMorphism_f {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    [Smooth Y.hom] [Projective Y.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : X ⟶ Y) :
    (pushforwardMorphism d e hXdim hYdim f).f =
      Correspondence.castDegree
        ((add_zero ((e : ℤ) - d)).trans (sub_zero ((e : ℤ) - d)).symm)
        (Correspondence.transpose Y X e d hYdim hXdim 0
          (Correspondence.rationalGraph f)) := sorry

/-- Proper pushforward of a codimension-`r` rational Chow cycle, represented by
composition with the transposed graph. -/
def cyclePushforward {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    [Smooth Y.hom] [Projective Y.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : X ⟶ Y)
    (r : ℤ) (alpha : Correspondence.Rational (SchemeOverField.point k) X r) :
    Correspondence.Rational (SchemeOverField.point k) Y
      (r + ((e : ℤ) - d)) :=
  Correspondence.composition (SchemeOverField.point k) X Y r ((e : ℤ) - d) alpha
    (Correspondence.castDegree (add_zero ((e : ℤ) - d))
      (Correspondence.transpose Y X e d hYdim hXdim 0
        (Correspondence.rationalGraph f)))

/-- Cycle pushforward is composition with the dimension-shifted transposed graph. -/
theorem cyclePushforward_def {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    [Smooth Y.hom] [Projective Y.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : X ⟶ Y)
    (r : ℤ) (alpha : Correspondence.Rational (SchemeOverField.point k) X r) :
    cyclePushforward d e hXdim hYdim f r alpha =
      Correspondence.composition (SchemeOverField.point k) X Y r ((e : ℤ) - d) alpha
        (Correspondence.castDegree (add_zero ((e : ℤ) - d))
          (Correspondence.transpose Y X e d hYdim hXdim 0
            (Correspondence.rationalGraph f))) := sorry

/-- The rational Chow cycle of the point is its identity graph correspondence. -/
def pointCycle : Correspondence.Rational (SchemeOverField.point k)
    (SchemeOverField.point k) 0 :=
  Correspondence.rationalGraph (𝟙 (SchemeOverField.point k))

/-- The point cycle is the rational graph of the identity of `Spec(k)`. -/
theorem pointCycle_def : pointCycle (k := k) =
    Correspondence.rationalGraph (𝟙 (SchemeOverField.point k)) := sorry

/-- The fundamental class of a smooth projective `d`-fold as a morphism from its
motive to `𝟙(-d)`. -/
def fundamentalMorphism
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    [EquidimensionalSpace X.left] (d : ℕ)
    (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞)) :
    h X ⟶ tateTwist (SchemeOverField.point k) (-(d : ℤ)) where
  f := Correspondence.castDegree (sub_zero (-(d : ℤ))).symm
    (Correspondence.fundamental
      ((⟨X, ⟨inferInstance, inferInstance⟩⟩ : Correspondence.Category k)) d)
  comm := sorry

/-- The underlying map of `fundamentalMorphism` is the fundamental Chow
correspondence. -/
theorem fundamentalMorphism_f
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    [EquidimensionalSpace X.left] (d : ℕ)
    (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞)) :
    (fundamentalMorphism X d hXdim).f =
      Correspondence.castDegree (sub_zero (-(d : ℤ))).symm
        (Correspondence.fundamental
          ((⟨X, ⟨inferInstance, inferInstance⟩⟩ : Correspondence.Category k)) d) := sorry

/-- The exterior product of two cycle morphisms before applying a realization. -/
def cycleExternalProductMorphism
    (X Y : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    [Smooth Y.hom] [Projective Y.hom] (r s : ℤ)
    (alpha : Correspondence.Rational (SchemeOverField.point k) X r)
    (beta : Correspondence.Rational (SchemeOverField.point k) Y s) :
    tateTwist (SchemeOverField.point k) (-(r + s)) ⟶ h X ⊗ h Y :=
  eqToHom (congrArg (tateTwist (SchemeOverField.point k))
      (Int.neg_add (a := r) (b := s))) ≫
    (Tate.tensorIso k (-r) (-s)).inv ≫
      (cycleMorphism X r alpha ⊗ₘ cycleMorphism Y s beta)

/-- The motivic intersection product is exterior product followed by the diagonal. -/
def cycleIntersectionMorphism
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] (r s : ℤ)
    (alpha : Correspondence.Rational (SchemeOverField.point k) X r)
    (beta : Correspondence.Rational (SchemeOverField.point k) X s) :
    tateTwist (SchemeOverField.point k) (-(r + s)) ⟶ h X :=
  cycleExternalProductMorphism X X r s alpha beta ≫ diagonalMultiplication X

/-- The cycle intersection morphism is exterior product followed by motivic
multiplication. -/
theorem cycleIntersectionMorphism_def
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] (r s : ℤ)
    (alpha : Correspondence.Rational (SchemeOverField.point k) X r)
    (beta : Correspondence.Rational (SchemeOverField.point k) X s) :
    cycleIntersectionMorphism X r s alpha beta =
      cycleExternalProductMorphism X X r s alpha beta ≫ diagonalMultiplication X := sorry

end ChowMotive

namespace WeilCohomology.MotivicRealization

open AlgebraicGeometry AlgebraicGeometry.Correspondence
open TopologicalSpace
open CategoryTheory.GradedObject
open CategoryTheory.GradedObject.Monoidal

variable {k : Type u} [Field k]
variable {F : Type v} [Field F] [CharZero F]

/-- A monoidal realization respects the explicit Koszul symmetry when its tensor comparison
intertwines the motivic braiding with `koszulBraidingHom`. -/
def IsKoszulBraided
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) [G.Monoidal] : Prop :=
  ∀ X Y,
    (Functor.Monoidal.μIso G X Y).hom ≫ G.map (β_ X Y).hom =
      koszulBraidingHom (G.obj X) (G.obj Y) ≫
        (Functor.Monoidal.μIso G Y X).hom

/-- Koszul compatibility is exactly the braiding-intertwining equation for the monoidal
comparison isomorphisms. -/
theorem isKoszulBraided_iff
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) [G.Monoidal] :
    IsKoszulBraided G ↔
      ∀ X Y,
        (Functor.Monoidal.μIso G X Y).hom ≫ G.map (β_ X Y).hom =
          koszulBraidingHom (G.obj X) (G.obj Y) ≫
            (Functor.Monoidal.μIso G Y X).hom := sorry

/-- The zero Tate twist and the untwisted motive have canonically equal realized
components, with the harmless degree-zero shift made explicit. -/
theorem untwistZero_component
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F))
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] (i : ℤ) :
    (G.obj (ChowMotive.tateTwist X 0)) i =
      (G.obj (ChowMotive.h X)) (i + 2 * 0) := sorry

/-- A coherent Tate normalization: besides `F[2] ≅ G(𝟙(1))`, it records the
component identifications with `F` and the degree shifts used to read realized Tate
twists as ordinary cohomological degrees. -/
structure TateNormalization
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) where
  /-- The chosen identification `F[2] ≅ G(𝟙(1))`. -/
  iso : (GradedObject.single (-2 : ℤ)).obj (ModuleCat.of F F) ≅
    G.obj (ChowMotive.tateTwist (SchemeOverField.point k) 1)
  /-- The normalized generator of the realization of `𝟙(-r)` in degree `2 * r`. -/
  degreeIso : ∀ r : ℤ, ModuleCat.of F F ≅
    (G.obj (ChowMotive.tateTwist (SchemeOverField.point k) (-r))) (2 * r)
  /-- Tate twisting a motive by `n` shifts its realized components by `2 * n`. -/
  untwistIso : ∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    (n i : ℤ), (G.obj (ChowMotive.tateTwist X n)) i ≅
      (G.obj (ChowMotive.h X)) (i + 2 * n)

namespace TateNormalization

/-- Construct a Tate normalization from explicit graded and componentwise comparison
isomorphisms. -/
def ofIso
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)}
    (e : (GradedObject.single (-2 : ℤ)).obj (ModuleCat.of F F) ≅
      G.obj (ChowMotive.tateTwist (SchemeOverField.point k) 1))
    (degreeIso : ∀ r : ℤ, ModuleCat.of F F ≅
      (G.obj (ChowMotive.tateTwist (SchemeOverField.point k) (-r))) (2 * r))
    (untwistIso : ∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
      (n i : ℤ), (G.obj (ChowMotive.tateTwist X n)) i ≅
        (G.obj (ChowMotive.h X)) (i + 2 * n)) :
    TateNormalization G where
  iso := e
  degreeIso := degreeIso
  untwistIso := untwistIso

/-- The isomorphism stored by `ofIso` is the supplied Tate identification. -/
theorem ofIso_iso
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)}
    (e : (GradedObject.single (-2 : ℤ)).obj (ModuleCat.of F F) ≅
      G.obj (ChowMotive.tateTwist (SchemeOverField.point k) 1))
    (degreeIso : ∀ r : ℤ, ModuleCat.of F F ≅
      (G.obj (ChowMotive.tateTwist (SchemeOverField.point k) (-r))) (2 * r))
    (untwistIso : ∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
      (n i : ℤ), (G.obj (ChowMotive.tateTwist X n)) i ≅
        (G.obj (ChowMotive.h X)) (i + 2 * n)) :
    (ofIso e degreeIso untwistIso).iso = e := sorry

/-- The degree comparison stored by `ofIso` is the supplied normalized Tate line. -/
theorem ofIso_degreeIso
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)}
    (e : (GradedObject.single (-2 : ℤ)).obj (ModuleCat.of F F) ≅
      G.obj (ChowMotive.tateTwist (SchemeOverField.point k) 1))
    (degreeIso : ∀ r : ℤ, ModuleCat.of F F ≅
      (G.obj (ChowMotive.tateTwist (SchemeOverField.point k) (-r))) (2 * r))
    (untwistIso : ∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
      (n i : ℤ), (G.obj (ChowMotive.tateTwist X n)) i ≅
        (G.obj (ChowMotive.h X)) (i + 2 * n)) :
    (ofIso e degreeIso untwistIso).degreeIso = degreeIso := sorry

end TateNormalization

/-- The canonical component map cancelling a Tate twist, built from the normalized
Tate generator, the graded tensor inclusion, the monoidal comparison of `G`, and
the motivic cancellation map. -/
def canonicalUntwistHom
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) [G.Monoidal]
    (normalization : TateNormalization G)
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] (n i : ℤ) :
    (G.obj (ChowMotive.tateTwist X n)) i ⟶
      (G.obj (ChowMotive.h X)) (i + 2 * n) :=
  (λ_ ((G.obj (ChowMotive.tateTwist X n)) i)).inv ≫
    ((normalization.degreeIso n).hom ⊗ₘ
      𝟙 ((G.obj (ChowMotive.tateTwist X n)) i)) ≫
      ιTensorObj
        (G.obj (ChowMotive.tateTwist (SchemeOverField.point k) (-n)))
        (G.obj (ChowMotive.tateTwist X n)) (2 * n) i (i + 2 * n)
        (add_comm (2 * n) i) ≫
        (Functor.Monoidal.μIso G
          (ChowMotive.tateTwist (SchemeOverField.point k) (-n))
          (ChowMotive.tateTwist X n)).hom (i + 2 * n) ≫
          (G.map (ChowMotive.Tate.untwistHom X n)) (i + 2 * n)

/-- The canonical untwisting map is the tensor composite determined by the chosen
normalized Tate generator. -/
theorem canonicalUntwistHom_def
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) [G.Monoidal]
    (normalization : TateNormalization G)
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] (n i : ℤ) :
    canonicalUntwistHom G normalization X n i =
      (λ_ ((G.obj (ChowMotive.tateTwist X n)) i)).inv ≫
        ((normalization.degreeIso n).hom ⊗ₘ
          𝟙 ((G.obj (ChowMotive.tateTwist X n)) i)) ≫
          ιTensorObj
            (G.obj (ChowMotive.tateTwist (SchemeOverField.point k) (-n)))
            (G.obj (ChowMotive.tateTwist X n)) (2 * n) i (i + 2 * n)
            (add_comm (2 * n) i) ≫
            (Functor.Monoidal.μIso G
              (ChowMotive.tateTwist (SchemeOverField.point k) (-n))
              (ChowMotive.tateTwist X n)).hom (i + 2 * n) ≫
              (G.map (ChowMotive.Tate.untwistHom X n)) (i + 2 * n) := sorry

/-- Coherence conditions saying that the chosen componentwise Tate identifications
come from the base normalization and respect the monoidal unit, tensor powers, and
geometric pullback. -/
structure TateNormalization.Coherent
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Monoidal]
    (normalization : TateNormalization G) : Prop where
  /-- The degree `-2` generator is the component of `F[2] ≅ G(𝟙(1))`. -/
  degreeIso_neg_one : normalization.degreeIso (-1) =
    (GradedObject.singleObjApplyIso (-2 : ℤ) (ModuleCat.of F F)).symm ≪≫
      asIso (normalization.iso.hom (-2))
  /-- The degree-zero generator is induced by the monoidal unit comparison. -/
  degreeIso_zero : (normalization.degreeIso 0).hom =
    GradedObject.Monoidal.tensorUnit₀.inv ≫
      (Functor.Monoidal.εIso G).hom 0 ≫
        (G.map (ChowMotive.Tate.zeroIso k).inv) 0
  /-- Tensor products of normalized generators agree with addition of Tate indices. -/
  degreeIso_add : ∀ r s : ℤ, (normalization.degreeIso (r + s)).hom =
    (λ_ (ModuleCat.of F F)).inv ≫
      ((normalization.degreeIso r).hom ⊗ₘ (normalization.degreeIso s).hom) ≫
        ιTensorObj
          (G.obj (ChowMotive.tateTwist (SchemeOverField.point k) (-r)))
          (G.obj (ChowMotive.tateTwist (SchemeOverField.point k) (-s)))
          (2 * r) (2 * s) (2 * (r + s)) (mul_add 2 r s).symm ≫
          (Functor.Monoidal.μIso G
            (ChowMotive.tateTwist (SchemeOverField.point k) (-r))
            (ChowMotive.tateTwist (SchemeOverField.point k) (-s))).hom (2 * (r + s)) ≫
            (G.map ((ChowMotive.Tate.tensorIso k (-r) (-s)).hom ≫
              eqToHom (congrArg (ChowMotive.tateTwist (SchemeOverField.point k))
                (Int.neg_add (a := r) (b := s))).symm)) (2 * (r + s))
  /-- Every untwisting comparison is the canonical composite induced by the
  normalized Tate generator and the monoidal structure of `G`. -/
  untwistIso_canonical : ∀ (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] (n i : ℤ),
    (normalization.untwistIso X n i).hom =
      canonicalUntwistHom G normalization X n i
  /-- Untwisting by zero is the canonical identity comparison. -/
  untwistIso_zero : ∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    (i : ℤ), (normalization.untwistIso X 0 i).hom =
      eqToHom (untwistZero_component G X i)
  /-- Untwisting is natural for geometric pullback morphisms. -/
  untwistIso_pullback : ∀ {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [Smooth Y.hom] [Projective Y.hom]
    (f : X ⟶ Y) (n i : ℤ),
    (G.map (ChowMotive.twistedPullbackMorphism f n)) i ≫
        (normalization.untwistIso X n i).hom =
      (normalization.untwistIso Y n i).hom ≫
        (G.map (ChowMotive.pullbackMorphism f)) (i + 2 * n)

/-- Coherence data for a Tate normalization of a strong monoidal realization. -/
def TateNormalization.Coherent.ofNormalization
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Monoidal]
    (normalization : TateNormalization G) : normalization.Coherent where
  degreeIso_neg_one := sorry
  degreeIso_zero := sorry
  degreeIso_add := sorry
  untwistIso_canonical := sorry
  untwistIso_zero := sorry
  untwistIso_pullback := sorry

namespace TateNormalization.Coherent

/-- The coherently normalized isomorphism from the Tate line `F[2]` to `G(𝟙(1))`. -/
def baseIso
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Monoidal]
    {normalization : TateNormalization G} (_ : normalization.Coherent) :
    (GradedObject.single (-2 : ℤ)).obj (ModuleCat.of F F) ≅
      G.obj (ChowMotive.tateTwist (SchemeOverField.point k) 1) :=
  normalization.iso

/-- The coherent base Tate isomorphism is the isomorphism stored by the normalization. -/
theorem baseIso_eq
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Monoidal]
    {normalization : TateNormalization G} (h : normalization.Coherent) :
    h.baseIso = normalization.iso := sorry

end TateNormalization.Coherent

/-- The contravariant graded cohomology functor induced by a motivic realization. -/
def cohomology
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) :
    (Correspondence.Graded.SchemeCategory k)ᵒᵖ ⥤ GradedObject ℤ (ModuleCat F) :=
  ChowMotive.hFunctor k ⋙ G

/-- On a smooth projective scheme, motivic cohomology is the realization of its motive. -/
theorem cohomology_obj
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F))
    (X : (Correspondence.Graded.SchemeCategory k)ᵒᵖ) :
    (cohomology G).obj X = G.obj (ChowMotive.h X.unop.scheme) := sorry

/-- The multiplicative unit of realized cohomology, obtained from the monoidal-unit
comparison and the motivic structure morphism. -/
def cohomologyUnit
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) [G.Monoidal]
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] :
    𝟙_ (GradedObject ℤ (ModuleCat F)) ⟶ G.obj (ChowMotive.h X) :=
  (Functor.Monoidal.εIso G).hom ≫ G.map (ChowMotive.unitMorphism X)

/-- The cohomological unit is the monoidal-unit comparison followed by the realized
structure morphism. -/
theorem cohomologyUnit_def
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) [G.Monoidal]
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] :
    cohomologyUnit G X =
      (Functor.Monoidal.εIso G).hom ≫ G.map (ChowMotive.unitMorphism X) := sorry

/-- Cup product is induced by the motivic diagonal after the monoidal comparison map. -/
def cupProduct
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) [G.Monoidal]
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] :
    G.obj (ChowMotive.h X) ⊗ G.obj (ChowMotive.h X) ⟶ G.obj (ChowMotive.h X) :=
  (Functor.Monoidal.μIso G (ChowMotive.h X) (ChowMotive.h X)).hom ≫
    G.map (ChowMotive.diagonalMultiplication X)

/-- The motivic cup product is the monoidal comparison followed by the realized diagonal. -/
theorem cupProduct_def
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) [G.Monoidal]
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] :
    cupProduct G X =
      (Functor.Monoidal.μIso G (ChowMotive.h X) (ChowMotive.h X)).hom ≫
        G.map (ChowMotive.diagonalMultiplication X) := sorry

/-- Multiplication of classes in degrees `i` and `j` lands in degree `i + j`. -/
def cupProductComponent
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) [G.Monoidal]
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] (i j : ℤ) :
    (G.obj (ChowMotive.h X)) i ⊗ (G.obj (ChowMotive.h X)) j ⟶
      (G.obj (ChowMotive.h X)) (i + j) :=
  ιTensorObj (G.obj (ChowMotive.h X)) (G.obj (ChowMotive.h X))
    i j (i + j) rfl ≫ (cupProduct G X) (i + j)

/-- The homogeneous cup-product component is induced by the graded multiplication. -/
theorem cupProductComponent_def
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) [G.Monoidal]
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] (i j : ℤ) :
    cupProductComponent G X i j =
      ιTensorObj (G.obj (ChowMotive.h X)) (G.obj (ChowMotive.h X))
        i j (i + j) rfl ≫ (cupProduct G X) (i + j) := sorry

/-- A normalized class represented by a morphism from `𝟙(-r)` is its degree-`2 * r`
component evaluated on the normalized Tate generator. -/
def normalizedClass
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F))
    (normalization : TateNormalization G) (r : ℤ)
    {M : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)}
    (alpha : ChowMotive.tateTwist (SchemeOverField.point k) (-r) ⟶ M) :
    ModuleCat.of F F ⟶ (G.obj M) (2 * r) :=
  (normalization.degreeIso r).hom ≫ (G.map alpha) (2 * r)

/-- A normalized motivic class is obtained from the Tate generator followed by the
degree component of the realized motive morphism. -/
theorem normalizedClass_apply
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F))
    (normalization : TateNormalization G) (r : ℤ)
    {M : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)}
    (alpha : ChowMotive.tateTwist (SchemeOverField.point k) (-r) ⟶ M) :
    normalizedClass G normalization r alpha =
      (normalization.degreeIso r).hom ≫ (G.map alpha) (2 * r) := sorry

/-- The degree-`2 * r` cycle class of a codimension-`r` rational Chow cycle, obtained
from `ChowMotive.cycleMorphism`. -/
def cycleClass
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) (normalization : TateNormalization G)
    [G.Linear ℚ]
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] (r : ℤ)
    : Correspondence.Rational (SchemeOverField.point k) X r →
      (ModuleCat.of F F ⟶ (G.obj (ChowMotive.h X)) (2 * r)) :=
  fun alpha ↦
    normalizedClass G normalization r (ChowMotive.cycleMorphism X r alpha)

/-- Cycle classes are the normalized degree components of realized Chow cycle
morphisms. -/
theorem cycleClass_apply
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) (normalization : TateNormalization G) [G.Linear ℚ]
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] (r : ℤ)
    (alpha : Correspondence.Rational (SchemeOverField.point k) X r) :
    cycleClass G normalization X r alpha =
      (normalization.degreeIso r).hom ≫
        (G.map (ChowMotive.cycleMorphism X r alpha)) (2 * r) := sorry

/-- The integral Chow cycle-class map, obtained by rationalizing an integral
correspondence and then applying the rational cycle-class map. -/
def integralCycleClass
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) (normalization : TateNormalization G) [G.Linear ℚ]
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] (r : ℤ) :
    Correspondence.Integral (SchemeOverField.point k) X r →
      (ModuleCat.of F F ⟶ (G.obj (ChowMotive.h X)) (2 * r)) :=
  fun alpha ↦
    cycleClass G normalization X r
      (ChowMotive.toRational (SchemeOverField.point k) X r alpha)

/-- Integral cycle classes are rational cycle classes precomposed with the canonical
map `alpha ↦ 1 ⊗ₜ alpha`. -/
theorem integralCycleClass_apply
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) (normalization : TateNormalization G) [G.Linear ℚ]
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] (r : ℤ)
    (alpha : Correspondence.Integral (SchemeOverField.point k) X r) :
    integralCycleClass G normalization X r alpha =
      cycleClass G normalization X r
        (ChowMotive.toRational (SchemeOverField.point k) X r alpha) := sorry

/-- Cohomological pullback is the realization of the graph correspondence. -/
def pullback
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [Smooth Y.hom] [Projective Y.hom]
    (f : X ⟶ Y) : G.obj (ChowMotive.h Y) ⟶ G.obj (ChowMotive.h X) :=
  G.map (ChowMotive.pullbackMorphism f)

/-- Pullback is `G` applied to the contravariant graph morphism. -/
theorem pullback_def
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [Smooth Y.hom] [Projective Y.hom]
    (f : X ⟶ Y) :
    pullback G f = G.map (ChowMotive.pullbackMorphism f) := sorry

/-- Poincaré pushforward on a homogeneous component is the realization of the
dimension-shifted transposed graph, followed by the Tate untwisting comparison. -/
def pushforward
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) (normalization : TateNormalization G)
    (X Y : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    [Smooth Y.hom] [Projective Y.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞))
    (f : X ⟶ Y) (i : ℤ) :
    (G.obj (ChowMotive.h X)) i ⟶
      (G.obj (ChowMotive.h Y)) (i + 2 * ((e : ℤ) - d)) :=
  (G.map (ChowMotive.pushforwardMorphism d e hXdim hYdim f)) i ≫
    (normalization.untwistIso Y ((e : ℤ) - d) i).hom

/-- The homogeneous pushforward is the transposed-graph realization followed by
Tate untwisting. -/
theorem pushforward_def
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) (normalization : TateNormalization G)
    (X Y : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    [Smooth Y.hom] [Projective Y.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞))
    (f : X ⟶ Y) (i : ℤ) :
    pushforward G normalization X Y d e hXdim hYdim f i =
      (G.map (ChowMotive.pushforwardMorphism d e hXdim hYdim f)) i ≫
        (normalization.untwistIso Y ((e : ℤ) - d) i).hom := sorry

/-- The Künneth isomorphism supplied by the strong monoidal structure of `G`. -/
def kunnethIso
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) [G.Monoidal]
    (A B : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) :
    G.obj A ⊗ G.obj B ≅ G.obj (A ⊗ B) :=
  Functor.Monoidal.μIso G A B

/-- The forward Künneth map is the monoidal comparison morphism of `G`. -/
theorem kunnethIso_hom
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) [G.Monoidal]
    (A B : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) :
    (kunnethIso G A B).hom = (Functor.Monoidal.μIso G A B).hom := sorry

/-- The geometric Künneth isomorphism for two smooth projective schemes. -/
def geometricKunnethIso
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) [G.Monoidal]
    (X Y : Correspondence.Category k) :
    G.obj (ChowMotive.h X.scheme) ⊗ G.obj (ChowMotive.h Y.scheme) ≅
      G.obj (ChowMotive.h (Correspondence.Category.product X Y).scheme) :=
  Functor.Monoidal.μIso G (ChowMotive.h X.scheme) (ChowMotive.h Y.scheme) ≪≫
    G.mapIso (ChowMotive.productComparisonIso X Y)

/-- The geometric Künneth map is the strong-monoidal comparison on the two motives. -/
theorem geometricKunnethIso_hom
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) [G.Monoidal]
    (X Y : Correspondence.Category k) :
    (geometricKunnethIso G X Y).hom =
      (Functor.Monoidal.μIso G
        (ChowMotive.h X.scheme) (ChowMotive.h Y.scheme)).hom ≫
        G.map (ChowMotive.productComparisonIso X Y).hom := sorry

/-- Pullback along the first projection from a geometric product. -/
def productFstPullback
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) (X Y : Correspondence.Category k) :
    G.obj (ChowMotive.h X.scheme) ⟶
      G.obj (ChowMotive.h (Correspondence.Category.product X Y).scheme) :=
  G.map (ChowMotive.pullbackMorphism
    (CategoryTheory.Limits.prod.fst :
      (Correspondence.Category.product X Y).scheme ⟶ X.scheme))

/-- First-projection pullback is the realization of its graph correspondence. -/
theorem productFstPullback_def
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) (X Y : Correspondence.Category k) :
    productFstPullback G X Y =
      G.map (@ChowMotive.pullbackMorphism k _
        (Correspondence.Category.product X Y).scheme X.scheme
        (Correspondence.Category.scheme_smooth (Correspondence.Category.product X Y))
        (Correspondence.Category.scheme_projective (Correspondence.Category.product X Y))
        (Correspondence.Category.scheme_smooth X)
        (Correspondence.Category.scheme_projective X)
        (CategoryTheory.Limits.prod.fst :
          (Correspondence.Category.product X Y).scheme ⟶ X.scheme)) := sorry

/-- Pullback along the second projection from a geometric product. -/
def productSndPullback
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) (X Y : Correspondence.Category k) :
    G.obj (ChowMotive.h Y.scheme) ⟶
      G.obj (ChowMotive.h (Correspondence.Category.product X Y).scheme) :=
  G.map (ChowMotive.pullbackMorphism
    (CategoryTheory.Limits.prod.snd :
      (Correspondence.Category.product X Y).scheme ⟶ Y.scheme))

/-- Second-projection pullback is the realization of its graph correspondence. -/
theorem productSndPullback_def
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) (X Y : Correspondence.Category k) :
    productSndPullback G X Y =
      G.map (@ChowMotive.pullbackMorphism k _
        (Correspondence.Category.product X Y).scheme Y.scheme
        (Correspondence.Category.scheme_smooth (Correspondence.Category.product X Y))
        (Correspondence.Category.scheme_projective (Correspondence.Category.product X Y))
        (Correspondence.Category.scheme_smooth Y)
        (Correspondence.Category.scheme_projective Y)
        (CategoryTheory.Limits.prod.snd :
          (Correspondence.Category.product X Y).scheme ⟶ Y.scheme)) := sorry

/-- Cup product on the motive of a geometric product. -/
def productCupProduct
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) [G.Monoidal]
    (X Y : Correspondence.Category k) :
    G.obj (ChowMotive.h (Correspondence.Category.product X Y).scheme) ⊗
        G.obj (ChowMotive.h (Correspondence.Category.product X Y).scheme) ⟶
      G.obj (ChowMotive.h (Correspondence.Category.product X Y).scheme) :=
  (Functor.Monoidal.μIso G
      (ChowMotive.h (Correspondence.Category.product X Y).scheme)
      (ChowMotive.h (Correspondence.Category.product X Y).scheme)).hom ≫
    G.map (ChowMotive.diagonalMultiplication
      (Correspondence.Category.product X Y).scheme)

/-- Product cup multiplication is the realized diagonal of the geometric product. -/
theorem productCupProduct_def
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) [G.Monoidal]
    (X Y : Correspondence.Category k) :
    productCupProduct G X Y =
      (Functor.Monoidal.μIso G
        (ChowMotive.h (Correspondence.Category.product X Y).scheme)
        (ChowMotive.h (Correspondence.Category.product X Y).scheme)).hom ≫
      G.map (ChowMotive.diagonalMultiplication
        (Correspondence.Category.product X Y).scheme) := sorry

/-- The exact pairing on `h(X)` and `h(X)(d)`, transported through the strong monoidal
realization. -/
@[implicit_reducible]
def mappedPairing
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) [G.Monoidal]
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    [EquidimensionalSpace X.left] (d : ℕ)
    (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞)) :
    ExactPairing (G.obj (ChowMotive.h X)) (G.obj (ChowMotive.tateTwist X d)) :=
  (ChowMotive.exactPairing X d hXdim).map G

/-- Evaluation in `mappedPairing` is the monoidal image of the motivic diagonal evaluation. -/
theorem mappedPairing_evaluation
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) [G.Monoidal]
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    [EquidimensionalSpace X.left] (d : ℕ)
    (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞)) :
    (mappedPairing G X d hXdim).evaluation' =
      (ChowMotive.exactPairing X d hXdim).mapEvaluation G := sorry

/-- The top-degree trace is the degree-`2 * d` component of the realized fundamental
correspondence, followed by the normalized identification of `𝟙(-d)` with `F`. -/
def integral
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) (normalization : TateNormalization G)
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    [EquidimensionalSpace X.left] (d : ℕ)
    (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞)) :
    (G.obj (ChowMotive.h X)) (2 * (d : ℤ)) ⟶ ModuleCat.of F F :=
  (G.map (ChowMotive.fundamentalMorphism X d hXdim)) (2 * (d : ℤ)) ≫
    (normalization.degreeIso d).inv

/-- The trace is induced by the fundamental Chow cycle in top cohomological degree. -/
theorem integral_apply
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) (normalization : TateNormalization G)
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    [EquidimensionalSpace X.left] (d : ℕ)
    (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞)) :
    integral G normalization X d hXdim =
      (G.map (ChowMotive.fundamentalMorphism X d hXdim)) (2 * (d : ℤ)) ≫
        (normalization.degreeIso d).inv := sorry

/-- The Poincaré pairing in complementary cohomological degrees is cup product followed
by the top-degree trace. -/
def poincarePairing
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) [G.Monoidal]
    (normalization : TateNormalization G)
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    [EquidimensionalSpace X.left] (d : ℕ)
    (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞)) (i : ℤ) :
    (G.obj (ChowMotive.h X)) (2 * (d : ℤ) - i) →ₗ[F]
      (G.obj (ChowMotive.h X)) i →ₗ[F] F :=
  TensorProduct.curry
    (CategoryTheory.GradedObject.Monoidal.ιTensorObj
        (G.obj (ChowMotive.h X)) (G.obj (ChowMotive.h X))
        (2 * (d : ℤ) - i) i (2 * (d : ℤ)) (sub_add_cancel _ _) ≫
      (cupProduct G X) (2 * (d : ℤ)) ≫
        integral G normalization X d hXdim).hom

/-- The Poincaré pairing evaluates by cup product and the normalized trace. -/
theorem poincarePairing_apply
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) [G.Monoidal]
    (normalization : TateNormalization G)
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    [EquidimensionalSpace X.left] (d : ℕ)
    (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞)) (i : ℤ) :
    poincarePairing G normalization X d hXdim i =
      TensorProduct.curry
        (CategoryTheory.GradedObject.Monoidal.ιTensorObj
            (G.obj (ChowMotive.h X)) (G.obj (ChowMotive.h X))
            (2 * (d : ℤ) - i) i (2 * (d : ℤ)) (sub_add_cancel _ _) ≫
          (cupProduct G X) (2 * (d : ℤ)) ≫
            integral G normalization X d hXdim).hom := sorry

/-- The degree identity used in the Poincaré adjunction formula for pushforward. -/
theorem pushforwardComplementary_degree (d e : ℕ) (i : ℤ) :
    ((2 * (d : ℤ) - i) + 2 * ((e : ℤ) - d)) + i = 2 * (e : ℤ) := sorry

/-- The explicit data (D1)--(D3) and exactly axioms (A)(a,b), (B), and (C)
produced by a normalized motivic realization. There are deliberately no fields for
cohomological range vanishing (A)(c) or top-trace invertibility (A)(d). -/
structure ClassicalCore
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) [G.Linear ℚ] [G.Monoidal] where
  /-- The coherent degree normalization of Tate twists. -/
  normalization : TateNormalization G
  /-- The Tate normalization respects the base isomorphism, monoidal tensor powers,
  and untwisting naturality. -/
  normalization_coherent : normalization.Coherent
  /-- Data (D1): contravariant graded cohomology. -/
  cohomology : (Correspondence.Graded.SchemeCategory k)ᵒᵖ ⥤
    GradedObject ℤ (ModuleCat F)
  /-- The cohomology functor is `ChowMotive.hFunctor k ⋙ G`. -/
  cohomology_eq : cohomology = MotivicRealization.cohomology G
  /-- Data (D1): the unit of the graded cohomology algebra. -/
  unit : ∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom],
    𝟙_ (GradedObject ℤ (ModuleCat F)) ⟶ G.obj (ChowMotive.h X)
  /-- The cohomological unit is induced by the motivic structure morphism. -/
  unit_eq : ∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom],
    unit X = MotivicRealization.cohomologyUnit G X
  /-- Data (D1): pullback along a geometric morphism. -/
  pullback : ∀ {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [Smooth Y.hom] [Projective Y.hom],
    (X ⟶ Y) → (G.obj (ChowMotive.h Y) ⟶ G.obj (ChowMotive.h X))
  /-- Pullback is realized by the graph correspondence. -/
  pullback_eq : ∀ {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [Smooth Y.hom] [Projective Y.hom]
    (f : X ⟶ Y), pullback f = MotivicRealization.pullback G f
  /-- Pullback by an identity is the identity. -/
  pullback_id : ∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom],
    pullback (𝟙 X) = 𝟙 (G.obj (ChowMotive.h X))
  /-- Contravariant pullback reverses composition. -/
  pullback_comp : ∀ {X Y Z : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [Smooth Y.hom] [Projective Y.hom]
    [Smooth Z.hom] [Projective Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z),
    pullback (f ≫ g) = pullback g ≫ pullback f
  /-- Data (D1): cup product induced by the diagonal. -/
  cupProduct : ∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom],
    G.obj (ChowMotive.h X) ⊗ G.obj (ChowMotive.h X) ⟶ G.obj (ChowMotive.h X)
  /-- The cup product is the canonical realized diagonal product. -/
  cupProduct_eq : ∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom],
    cupProduct X = MotivicRealization.cupProduct G X
  /-- The cohomological unit is a left unit for cup product. -/
  cupProduct_unit_left : ∀ (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom],
    (unit X ⊗ₘ 𝟙 (G.obj (ChowMotive.h X))) ≫ cupProduct X =
      (λ_ (G.obj (ChowMotive.h X))).hom
  /-- The cohomological unit is a right unit for cup product. -/
  cupProduct_unit_right : ∀ (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom],
    (𝟙 (G.obj (ChowMotive.h X)) ⊗ₘ unit X) ≫ cupProduct X =
      (ρ_ (G.obj (ChowMotive.h X))).hom
  /-- Cup product is associative. -/
  cupProduct_assoc : ∀ (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom],
    (α_ (G.obj (ChowMotive.h X)) (G.obj (ChowMotive.h X))
        (G.obj (ChowMotive.h X))).hom ≫
        (𝟙 (G.obj (ChowMotive.h X)) ⊗ₘ cupProduct X) ≫ cupProduct X =
      (cupProduct X ⊗ₘ 𝟙 (G.obj (ChowMotive.h X))) ≫ cupProduct X
  /-- Cup product sends homogeneous degrees `i` and `j` to degree `i + j`. -/
  cupProduct_degree : ∀ (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] (i j : ℤ),
    ιTensorObj (G.obj (ChowMotive.h X)) (G.obj (ChowMotive.h X))
        i j (i + j) rfl ≫ (cupProduct X) (i + j) =
      MotivicRealization.cupProductComponent G X i j
  /-- Cup product is graded commutative for the Koszul symmetry. -/
  gradedComm : ∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom],
    koszulBraidingHom (G.obj (ChowMotive.h X)) (G.obj (ChowMotive.h X)) ≫
      cupProduct X = cupProduct X
  /-- Pullback preserves the cohomological unit. -/
  pullback_unit : ∀ {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [Smooth Y.hom] [Projective Y.hom]
    (f : X ⟶ Y), unit Y ≫ pullback f = unit X
  /-- Pullback preserves cup products. -/
  pullback_mul : ∀ {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [Smooth Y.hom] [Projective Y.hom]
    (f : X ⟶ Y),
    (pullback f ⊗ₘ pullback f) ≫ cupProduct X = cupProduct Y ≫ pullback f
  /-- Data (D2): a codimension-`r` Chow cycle gives a class in degree `2 * r`. -/
  cycleClass : ∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    (r : ℤ), Correspondence.Rational (SchemeOverField.point k) X r →
      (ModuleCat.of F F ⟶ (G.obj (ChowMotive.h X)) (2 * r))
  /-- Cycle classes are obtained from `ChowMotive.cycleMorphism`. -/
  cycleClass_eq : ∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    (r : ℤ) (alpha : Correspondence.Rational (SchemeOverField.point k) X r),
    cycleClass X r alpha = MotivicRealization.cycleClass G normalization X r alpha
  /-- Data (D2): integral Chow classes map to cohomology after rationalization. -/
  integralCycleClass : ∀ (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] (r : ℤ),
    Correspondence.Integral (SchemeOverField.point k) X r →
      (ModuleCat.of F F ⟶ (G.obj (ChowMotive.h X)) (2 * r))
  /-- The integral cycle-class map is the rational map precomposed with
  `alpha ↦ 1 ⊗ₜ alpha`. -/
  integralCycleClass_eq : ∀ (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] (r : ℤ)
    (alpha : Correspondence.Integral (SchemeOverField.point k) X r),
    integralCycleClass X r alpha =
      cycleClass X r
        (ChowMotive.toRational (SchemeOverField.point k) X r alpha)
  /-- Data (D3): the trace from top-degree cohomology to `F`. -/
  integral : ∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    [EquidimensionalSpace X.left] (d : ℕ),
    topologicalKrullDim X.left = (d : WithBot ℕ∞) →
      ((G.obj (ChowMotive.h X)) (2 * (d : ℤ)) ⟶ ModuleCat.of F F)
  /-- The trace is the normalized realization of the fundamental Chow class. -/
  integral_eq : ∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    [EquidimensionalSpace X.left] (d : ℕ)
    (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞)),
    integral X d hXdim = MotivicRealization.integral G normalization X d hXdim
  /-- Poincaré-derived pushforward with its prescribed dimension shift. -/
  pushforward : ∀ (X Y : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    [Smooth Y.hom] [Projective Y.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : X ⟶ Y) (i : ℤ),
    (G.obj (ChowMotive.h X)) i ⟶
      (G.obj (ChowMotive.h Y)) (i + 2 * ((e : ℤ) - d))
  /-- Pushforward is the normalized realization of the transposed graph. -/
  pushforward_eq : ∀ (X Y : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    [Smooth Y.hom] [Projective Y.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : X ⟶ Y) (i : ℤ),
    pushforward X Y d e hXdim hYdim f i =
      MotivicRealization.pushforward G normalization X Y d e hXdim hYdim f i
  /-- Pushforward is adjoint to pullback for cup product and the Poincaré traces. -/
  pushforward_adjoint : ∀ (X Y : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    [Smooth Y.hom] [Projective Y.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : X ⟶ Y)
    (i : ℤ) (a : ModuleCat.of F F ⟶
      (G.obj (ChowMotive.h X)) (2 * (d : ℤ) - i))
    (b : ModuleCat.of F F ⟶ (G.obj (ChowMotive.h Y)) i),
    (λ_ (ModuleCat.of F F)).inv ≫
        (a ⊗ₘ (b ≫ (pullback f) i)) ≫
          ιTensorObj (G.obj (ChowMotive.h X)) (G.obj (ChowMotive.h X))
            (2 * (d : ℤ) - i) i (2 * (d : ℤ)) (sub_add_cancel _ _) ≫
            (cupProduct X) (2 * (d : ℤ)) ≫ integral X d hXdim =
      (λ_ (ModuleCat.of F F)).inv ≫
        ((a ≫ pushforward X Y d e hXdim hYdim f (2 * (d : ℤ) - i)) ⊗ₘ b) ≫
          ιTensorObj (G.obj (ChowMotive.h Y)) (G.obj (ChowMotive.h Y))
            ((2 * (d : ℤ) - i) + 2 * ((e : ℤ) - d)) i (2 * (e : ℤ))
              (pushforwardComplementary_degree d e i) ≫
            (cupProduct Y) (2 * (e : ℤ)) ≫ integral Y e hYdim
  /-- The exact motivic pairings transported through `G`. -/
  motivicPairing : ∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    [EquidimensionalSpace X.left] (d : ℕ),
    topologicalKrullDim X.left = (d : WithBot ℕ∞) →
      ExactPairing (G.obj (ChowMotive.h X)) (G.obj (ChowMotive.tateTwist X d))
  /-- The stored motivic pairing is the image of motivic duality. -/
  motivicPairing_eq : ∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    [EquidimensionalSpace X.left] (d : ℕ)
    (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞)),
    motivicPairing X d hXdim = MotivicRealization.mappedPairing G X d hXdim
  /-- The complementary-degree Poincaré pairing obtained from cup product and trace. -/
  poincarePairing : ∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    [EquidimensionalSpace X.left] (d : ℕ),
    topologicalKrullDim X.left = (d : WithBot ℕ∞) → ∀ i : ℤ,
      (G.obj (ChowMotive.h X)) (2 * (d : ℤ) - i) →ₗ[F]
        (G.obj (ChowMotive.h X)) i →ₗ[F] F
  /-- The stored Poincaré pairing is cup product followed by the trace. -/
  poincarePairing_eq : ∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    [EquidimensionalSpace X.left] (d : ℕ)
    (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞)) (i : ℤ),
    poincarePairing X d hXdim i =
      MotivicRealization.poincarePairing G normalization X d hXdim i
  /-- The Künneth comparison isomorphisms supplied by `G` (B). -/
  kunnethIso : ∀ A B : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k),
    G.obj A ⊗ G.obj B ≅ G.obj (A ⊗ B)
  /-- The stored Künneth maps are the strong-monoidal comparison isomorphisms. -/
  kunnethIso_eq : ∀ A B, kunnethIso A B = MotivicRealization.kunnethIso G A B
  /-- Axiom (B): the Künneth isomorphism for the geometric product. -/
  geometricKunnethIso : ∀ X Y : Correspondence.Category k,
    G.obj (ChowMotive.h X.scheme) ⊗ G.obj (ChowMotive.h Y.scheme) ≅
      G.obj (ChowMotive.h (Correspondence.Category.product X Y).scheme)
  /-- The geometric Künneth isomorphism is induced by the monoidal comparison. -/
  geometricKunnethIso_eq : ∀ X Y,
    geometricKunnethIso X Y = MotivicRealization.geometricKunnethIso G X Y
  /-- On pure tensors, geometric Künneth is pullback along the two projections followed
  by cup product. -/
  geometricKunneth_pullback_cup : ∀ X Y : Correspondence.Category k,
    (geometricKunnethIso X Y).hom =
      (MotivicRealization.productFstPullback G X Y ⊗ₘ
        MotivicRealization.productSndPullback G X Y) ≫
          MotivicRealization.productCupProduct G X Y
  /-- The realization uses the Koszul rather than unsigned symmetry. -/
  koszul : IsKoszulBraided G
  /-- Every homogeneous cohomology group is finite-dimensional (A)(a). -/
  finiteDimensional : ∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    (i : ℤ), FiniteDimensional F ((G.obj (ChowMotive.h X)) i)
  /-- The complementary-degree Poincaré pairing is perfect (A)(b). -/
  poincarePerfect : ∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    [EquidimensionalSpace X.left] (d : ℕ)
    (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞)) (i : ℤ),
    Function.Bijective (poincarePairing X d hXdim i)
  /-- Cycle classes commute with geometric pullback (C)(a). -/
  cycleClass_pullback : ∀ {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [Smooth Y.hom] [Projective Y.hom]
    (f : X ⟶ Y) (r : ℤ)
    (beta : Correspondence.Rational (SchemeOverField.point k) Y r),
    cycleClass X r (ChowMotive.cyclePullback f r beta) =
      cycleClass Y r beta ≫ (pullback f) (2 * r)
  /-- Cycle classes commute with Poincaré pushforward (C)(b). -/
  cycleClass_pushforward : ∀ {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    [Smooth Y.hom] [Projective Y.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : X ⟶ Y)
    (r : ℤ) (alpha : Correspondence.Rational (SchemeOverField.point k) X r),
    cycleClass Y (r + ((e : ℤ) - d))
        (ChowMotive.cyclePushforward d e hXdim hYdim f r alpha) =
      cycleClass X r alpha ≫ pushforward X Y d e hXdim hYdim f (2 * r) ≫
        eqToHom (congrArg (fun j ↦ (G.obj (ChowMotive.h Y)) j)
          (mul_add 2 r ((e : ℤ) - d)).symm)
  /-- Exterior products of Chow cycles map to tensor products of their classes (C)(c). -/
  cycleClass_externalProduct : ∀
    (X Y : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    [Smooth Y.hom] [Projective Y.hom] (r s : ℤ)
    (alpha : Correspondence.Rational (SchemeOverField.point k) X r)
    (beta : Correspondence.Rational (SchemeOverField.point k) Y s),
    normalizedClass G normalization (r + s)
        (ChowMotive.cycleExternalProductMorphism X Y r s alpha beta) =
      (λ_ (ModuleCat.of F F)).inv ≫
        (cycleClass X r alpha ⊗ₘ cycleClass Y s beta) ≫
          ιTensorObj (G.obj (ChowMotive.h X)) (G.obj (ChowMotive.h Y))
            (2 * r) (2 * s) (2 * (r + s)) (mul_add 2 r s).symm ≫
            (kunnethIso (ChowMotive.h X) (ChowMotive.h Y)).hom (2 * (r + s))
  /-- Intersection products of Chow cycles map to cup products (C)(c). -/
  cycleClass_mul : ∀ (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    (r s : ℤ) (alpha : Correspondence.Rational (SchemeOverField.point k) X r)
    (beta : Correspondence.Rational (SchemeOverField.point k) X s),
    normalizedClass G normalization (r + s)
        (ChowMotive.cycleIntersectionMorphism X r s alpha beta) =
      (λ_ (ModuleCat.of F F)).inv ≫
        (cycleClass X r alpha ⊗ₘ cycleClass X s beta) ≫
          ιTensorObj (G.obj (ChowMotive.h X)) (G.obj (ChowMotive.h X))
            (2 * r) (2 * s) (2 * (r + s)) (mul_add 2 r s).symm ≫
            (cupProduct X) (2 * (r + s))
  /-- The point cycle has trace one (C)(d). -/
  point_normalization :
    cycleClass (SchemeOverField.point k) 0 ChowMotive.pointCycle ≫
      integral (SchemeOverField.point k) 0 ChowMotive.point_dimension =
        𝟙 (ModuleCat.of F F)

namespace ClassicalCore

/-- Build the classical core from a chosen Tate normalization and Koszul-compatible
monoidal realization; every non-`Prop` field is a canonical construction from `G`. -/
def ofNormalization
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) [G.Linear ℚ] [G.Monoidal]
    (normalization : TateNormalization G) (h_normalization : normalization.Coherent)
    (h_koszul : IsKoszulBraided G) :
    ClassicalCore G where
  normalization := normalization
  normalization_coherent := h_normalization
  cohomology := MotivicRealization.cohomology G
  cohomology_eq := sorry
  unit := MotivicRealization.cohomologyUnit G
  unit_eq := sorry
  pullback := MotivicRealization.pullback G
  pullback_eq := sorry
  pullback_id := sorry
  pullback_comp := sorry
  cupProduct := MotivicRealization.cupProduct G
  cupProduct_eq := sorry
  cupProduct_unit_left := sorry
  cupProduct_unit_right := sorry
  cupProduct_assoc := sorry
  cupProduct_degree := sorry
  gradedComm := sorry
  pullback_unit := sorry
  pullback_mul := sorry
  cycleClass := MotivicRealization.cycleClass G normalization
  cycleClass_eq := sorry
  integralCycleClass := MotivicRealization.integralCycleClass G normalization
  integralCycleClass_eq := sorry
  integral := MotivicRealization.integral G normalization
  integral_eq := sorry
  pushforward := MotivicRealization.pushforward G normalization
  pushforward_eq := sorry
  pushforward_adjoint := sorry
  motivicPairing := MotivicRealization.mappedPairing G
  motivicPairing_eq := sorry
  poincarePairing := MotivicRealization.poincarePairing G normalization
  poincarePairing_eq := sorry
  kunnethIso := MotivicRealization.kunnethIso G
  kunnethIso_eq := sorry
  geometricKunnethIso := MotivicRealization.geometricKunnethIso G
  geometricKunnethIso_eq := sorry
  geometricKunneth_pullback_cup := sorry
  koszul := h_koszul
  finiteDimensional := sorry
  poincarePerfect := sorry
  cycleClass_pullback := sorry
  cycleClass_pushforward := sorry
  cycleClass_externalProduct := sorry
  cycleClass_mul := sorry
  point_normalization := sorry

/-- The normalization of `ofNormalization` is the supplied Tate identification. -/
theorem ofNormalization_normalization
    (G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)) [G.Linear ℚ] [G.Monoidal]
    (normalization : TateNormalization G) (h_normalization : normalization.Coherent)
    (h_koszul : IsKoszulBraided G) :
    (ofNormalization G normalization h_normalization h_koszul).normalization =
      normalization := sorry

/-- Data (D1): the stored cohomology functor is `ChowMotive.hFunctor k ⋙ G`. -/
theorem cohomology_obj
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G) (X : (Correspondence.Graded.SchemeCategory k)ᵒᵖ) :
    C.cohomology.obj X = G.obj (ChowMotive.h X.unop.scheme) := sorry

/-- Data (D1): the core unit is induced by the motivic structure morphism. -/
theorem unit_def
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G) (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] :
    C.unit X = MotivicRealization.cohomologyUnit G X := sorry

/-- Data (D1): core pullback is realization of the graph correspondence. -/
theorem pullback_apply
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G) {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [Smooth Y.hom] [Projective Y.hom]
    (f : X ⟶ Y) : C.pullback f = G.map (ChowMotive.pullbackMorphism f) := sorry

/-- Data (D1): pullback by an identity morphism is the identity. -/
theorem pullback_id_spec
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G) (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] :
    C.pullback (𝟙 X) = 𝟙 (G.obj (ChowMotive.h X)) := sorry

/-- Data (D1): contravariant pullback reverses composition. -/
theorem pullback_comp_spec
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G) {X Y Z : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [Smooth Y.hom] [Projective Y.hom]
    [Smooth Z.hom] [Projective Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) :
    C.pullback (f ≫ g) = C.pullback g ≫ C.pullback f := sorry

/-- Data (D1): the core cup product is induced by the motivic diagonal. -/
theorem cupProduct_def
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G) (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] :
    C.cupProduct X = MotivicRealization.cupProduct G X := sorry

/-- Data (D1): the cohomological unit is a left unit for cup product. -/
theorem cupProduct_unit_left_spec
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G) (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] :
    (C.unit X ⊗ₘ 𝟙 (G.obj (ChowMotive.h X))) ≫ C.cupProduct X =
      (λ_ (G.obj (ChowMotive.h X))).hom := sorry

/-- Data (D1): cup product is associative. -/
theorem cupProduct_assoc_spec
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G) (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] :
    (α_ (G.obj (ChowMotive.h X)) (G.obj (ChowMotive.h X))
        (G.obj (ChowMotive.h X))).hom ≫
        (𝟙 (G.obj (ChowMotive.h X)) ⊗ₘ C.cupProduct X) ≫ C.cupProduct X =
      (C.cupProduct X ⊗ₘ 𝟙 (G.obj (ChowMotive.h X))) ≫ C.cupProduct X := sorry

/-- Data (D1): the component cup product adds homogeneous degrees. -/
theorem cupProduct_degree_spec
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G) (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] (i j : ℤ) :
    ιTensorObj (G.obj (ChowMotive.h X)) (G.obj (ChowMotive.h X))
        i j (i + j) rfl ≫ (C.cupProduct X) (i + j) =
      MotivicRealization.cupProductComponent G X i j := sorry

/-- Data (D1): pullback preserves cup products. -/
theorem pullback_mul_spec
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G) {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [Smooth Y.hom] [Projective Y.hom]
    (f : X ⟶ Y) :
    (C.pullback f ⊗ₘ C.pullback f) ≫ C.cupProduct X =
      C.cupProduct Y ≫ C.pullback f := sorry

/-- Data (D1): the core cup product is commutative for the Koszul symmetry. -/
theorem gradedComm_spec
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G) (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] :
    koszulBraidingHom (G.obj (ChowMotive.h X)) (G.obj (ChowMotive.h X)) ≫
      C.cupProduct X = C.cupProduct X := sorry

/-- Data (D2): the core cycle class is induced by `ChowMotive.cycleMorphism`. -/
theorem cycleClass_apply
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G) (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] (r : ℤ)
    (alpha : Correspondence.Rational (SchemeOverField.point k) X r) :
    C.cycleClass X r alpha =
      (C.normalization.degreeIso r).hom ≫
        (G.map (ChowMotive.cycleMorphism X r alpha)) (2 * r) := sorry

/-- Data (D2): the integral cycle-class map is obtained by rationalizing the Chow
correspondence before applying the rational cycle-class map. -/
theorem integralCycleClass_apply
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G) (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] (r : ℤ)
    (alpha : Correspondence.Integral (SchemeOverField.point k) X r) :
    C.integralCycleClass X r alpha =
      C.cycleClass X r
        (ChowMotive.toRational (SchemeOverField.point k) X r alpha) := sorry

/-- Data (D3): the core trace is induced by the fundamental Chow class. -/
theorem integral_apply
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G) (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    (d : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞)) :
    C.integral X d hXdim =
      (G.map (ChowMotive.fundamentalMorphism X d hXdim)) (2 * (d : ℤ)) ≫
        (C.normalization.degreeIso d).inv := sorry

/-- Axiom (A)(a): every homogeneous cohomology group is finite-dimensional. -/
theorem finiteDimensional_spec
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G) (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] (i : ℤ) :
    FiniteDimensional F ((G.obj (ChowMotive.h X)) i) := sorry

/-- Axiom (A)(b): the complementary-degree Poincaré pairing is perfect. -/
theorem poincarePerfect_spec
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G) (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    (d : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞)) (i : ℤ) :
    Function.Bijective (C.poincarePairing X d hXdim i) := sorry

/-- Axiom (B): the forward Künneth map is the monoidal comparison of `G`. -/
theorem kunnethIso_hom
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G)
    (A B : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) :
    (C.kunnethIso A B).hom = (Functor.Monoidal.μIso G A B).hom := sorry

/-- Axiom (B): geometric Künneth is the cup product of pullbacks from the two
projections. -/
theorem geometricKunneth_pullback_cup_spec
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G) (X Y : Correspondence.Category k) :
    (C.geometricKunnethIso X Y).hom =
      (MotivicRealization.productFstPullback G X Y ⊗ₘ
        MotivicRealization.productSndPullback G X Y) ≫
          MotivicRealization.productCupProduct G X Y := sorry

/-- The core pushforward is the Poincaré transpose realized from the transposed graph. -/
theorem pushforward_apply
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G) (X Y : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    [Smooth Y.hom] [Projective Y.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞))
    (f : X ⟶ Y) (i : ℤ) :
    C.pushforward X Y d e hXdim hYdim f i =
      MotivicRealization.pushforward G C.normalization X Y d e hXdim hYdim f i := sorry

/-- Axiom (C)(b): pushforward is adjoint to pullback for the Poincaré pairings. -/
theorem pushforward_adjoint_spec
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G) (X Y : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    [Smooth Y.hom] [Projective Y.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : X ⟶ Y)
    (i : ℤ) (a : ModuleCat.of F F ⟶
      (G.obj (ChowMotive.h X)) (2 * (d : ℤ) - i))
    (b : ModuleCat.of F F ⟶ (G.obj (ChowMotive.h Y)) i) :
    (λ_ (ModuleCat.of F F)).inv ≫
        (a ⊗ₘ (b ≫ (C.pullback f) i)) ≫
          ιTensorObj (G.obj (ChowMotive.h X)) (G.obj (ChowMotive.h X))
            (2 * (d : ℤ) - i) i (2 * (d : ℤ)) (sub_add_cancel _ _) ≫
            (C.cupProduct X) (2 * (d : ℤ)) ≫ C.integral X d hXdim =
      (λ_ (ModuleCat.of F F)).inv ≫
        ((a ≫ C.pushforward X Y d e hXdim hYdim f (2 * (d : ℤ) - i)) ⊗ₘ b) ≫
          ιTensorObj (G.obj (ChowMotive.h Y)) (G.obj (ChowMotive.h Y))
            ((2 * (d : ℤ) - i) + 2 * ((e : ℤ) - d)) i (2 * (e : ℤ))
              (pushforwardComplementary_degree d e i) ≫
            (C.cupProduct Y) (2 * (e : ℤ)) ≫ C.integral Y e hYdim := sorry

/-- Axiom (C)(a): cycle classes commute with geometric pullback. -/
theorem cycleClass_pullback_spec
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G) {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [Smooth Y.hom] [Projective Y.hom]
    (f : X ⟶ Y) (r : ℤ)
    (beta : Correspondence.Rational (SchemeOverField.point k) Y r) :
    C.cycleClass X r (ChowMotive.cyclePullback f r beta) =
      C.cycleClass Y r beta ≫ (C.pullback f) (2 * r) := sorry

/-- Axiom (C)(b): cycle classes commute with Poincaré pushforward. -/
theorem cycleClass_pushforward_spec
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G) {X Y : SchemeOverField k}
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    [Smooth Y.hom] [Projective Y.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : X ⟶ Y)
    (r : ℤ) (alpha : Correspondence.Rational (SchemeOverField.point k) X r) :
    C.cycleClass Y (r + ((e : ℤ) - d))
        (ChowMotive.cyclePushforward d e hXdim hYdim f r alpha) =
      C.cycleClass X r alpha ≫ C.pushforward X Y d e hXdim hYdim f (2 * r) ≫
        eqToHom (congrArg (fun j ↦ (G.obj (ChowMotive.h Y)) j)
          (mul_add 2 r ((e : ℤ) - d)).symm) := sorry

/-- Axiom (C)(c), exterior-product form: Künneth carries the tensor of two cycle
classes to the class of their exterior product. -/
theorem cycleClass_externalProduct_spec
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G)
    (X Y : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    [Smooth Y.hom] [Projective Y.hom] (r s : ℤ)
    (alpha : Correspondence.Rational (SchemeOverField.point k) X r)
    (beta : Correspondence.Rational (SchemeOverField.point k) Y s) :
    normalizedClass G C.normalization (r + s)
        (ChowMotive.cycleExternalProductMorphism X Y r s alpha beta) =
      (λ_ (ModuleCat.of F F)).inv ≫
        (C.cycleClass X r alpha ⊗ₘ C.cycleClass Y s beta) ≫
          ιTensorObj (G.obj (ChowMotive.h X)) (G.obj (ChowMotive.h Y))
            (2 * r) (2 * s) (2 * (r + s)) (mul_add 2 r s).symm ≫
            (C.kunnethIso (ChowMotive.h X) (ChowMotive.h Y)).hom (2 * (r + s)) := sorry

/-- Axiom (C)(c), intersection form: cycle classes carry intersection products to
cup products. -/
theorem cycleClass_mul_spec
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G) (X : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom]
    (r s : ℤ) (alpha : Correspondence.Rational (SchemeOverField.point k) X r)
    (beta : Correspondence.Rational (SchemeOverField.point k) X s) :
    normalizedClass G C.normalization (r + s)
        (ChowMotive.cycleIntersectionMorphism X r s alpha beta) =
      (λ_ (ModuleCat.of F F)).inv ≫
        (C.cycleClass X r alpha ⊗ₘ C.cycleClass X s beta) ≫
          ιTensorObj (G.obj (ChowMotive.h X)) (G.obj (ChowMotive.h X))
            (2 * r) (2 * s) (2 * (r + s)) (mul_add 2 r s).symm ≫
            (C.cupProduct X) (2 * (r + s)) := sorry

/-- Axiom (C)(d): the point cycle has normalized trace one. -/
theorem point_normalization_spec
    {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
      GradedObject ℤ (ModuleCat F)} [G.Linear ℚ] [G.Monoidal]
    (C : ClassicalCore G) :
    C.cycleClass (SchemeOverField.point k) 0 ChowMotive.pointCycle ≫
      C.integral (SchemeOverField.point k) 0 ChowMotive.point_dimension =
        𝟙 (ModuleCat.of F F) := sorry

end ClassicalCore


/-- A ℚ-linear strong monoidal functor from Chow motives over an algebraically closed
field to graded vector spaces over a characteristic-zero field, compatible with the
Koszul symmetry and concentrating the image of `𝟙(1)` in degree `-2`, determines
classical Weil data (D1)--(D3) satisfying axioms (A)(a), (A)(b), (B), and (C),
without asserting (A)(c) or (A)(d). -/
theorem existsClassicalCore
    {k : Type u} [Field k] [IsAlgClosed k]
    {F : Type v} [Field F] [CharZero F]
    (G : ChowMotive k
      (fun _ ↦ AlgebraicGeometry.Correspondence.GradedCategory k) ⥤
        GradedObject ℤ (ModuleCat F))
    [G.Linear ℚ] [G.Monoidal] (h_koszul : IsKoszulBraided G)
    (h_tate : ∀ i : ℤ, i ≠ -2 →
      IsZero ((G.obj (ChowMotive.tateTwist (SchemeOverField.point k) 1)) i)) :
    Nonempty (ClassicalCore G) := sorry

/-- A ℚ-linear strong monoidal functor from Chow motives over an arbitrary field
to graded vector spaces over a characteristic-zero field, compatible with the
Koszul symmetry and concentrating the image of `𝟙(1)` in degree `-2`, determines
classical Weil data (D0)--(D3) satisfying axioms (A)(a), (A)(b), (B), and (C),
without asserting (A)(c) or (A)(d). -/
theorem existsClassicalCore_ofField
    {k : Type u} [Field k]
    {F : Type v} [Field F] [CharZero F]
    (G : ChowMotive k
      (fun _ ↦ AlgebraicGeometry.Correspondence.GradedCategory k) ⥤
        GradedObject ℤ (ModuleCat F))
    [G.Linear ℚ] [G.Monoidal] (h_koszul : IsKoszulBraided G)
    (h_tate : ∀ i : ℤ, i ≠ -2 →
      IsZero ((G.obj (ChowMotive.tateTwist (SchemeOverField.point k) 1)) i)) :
    Nonempty (ClassicalCore G) := sorry

end WeilCohomology.MotivicRealization
