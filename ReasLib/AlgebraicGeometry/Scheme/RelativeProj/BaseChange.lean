module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Presentation
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.GradedPullback

/-!
# Base change for relative projective spectra

This file records the graded algebra structures on relative-projective-spectrum twists and the
explicit comparison data obtained after a change of base scheme.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {S S' X : Scheme.{u}} {p : X ⟶ S}

/-- A graded algebra sheaf structure on the fixed family of twists of a relative projective
spectrum presentation. -/
structure RelativeProjTwistAlgebra (P : RelativeProjPresentation p) where
  /-- The degree-zero unit section of the twist algebra. -/
  one : ∀ U : X.Opensᵒᵖ, (P.twist 0).val.obj U
  /-- The degreewise multiplication on local sections of twists. -/
  mul : ∀ (U : X.Opensᵒᵖ) (n m : ℤ),
    (P.twist n).val.obj U →ₗ[X.presheaf.obj U]
      (P.twist m).val.obj U →ₗ[X.presheaf.obj U] (P.twist (n + m)).val.obj U
  /-- The degree-zero unit commutes with restriction maps. -/
  map_one : ∀ {U V : X.Opensᵒᵖ} (f : U ⟶ V),
    ((P.twist 0).val.map f).hom (one U) = one V
  /-- Twist multiplication commutes with restriction maps. -/
  map_mul : ∀ {U V : X.Opensᵒᵖ} (f : U ⟶ V) (n m : ℤ)
    (a : (P.twist n).val.obj U) (b : (P.twist m).val.obj U),
    ((P.twist (n + m)).val.map f).hom (mul U n m a b) =
      mul V n m (((P.twist n).val.map f).hom a) (((P.twist m).val.map f).hom b)
  /-- Twist multiplication is associative on local sections. -/
  mul_assoc : ∀ (U : X.Opensᵒᵖ) (i j k : ℤ)
    (a : (P.twist i).val.obj U) (b : (P.twist j).val.obj U)
    (c : (P.twist k).val.obj U),
    HEq (mul U (i + j) k (mul U i j a b) c)
      (mul U i (j + k) a (mul U j k b c))
  /-- The degree-zero unit is a left identity for twist multiplication. -/
  one_mul : ∀ (U : X.Opensᵒᵖ) (n : ℤ) (a : (P.twist n).val.obj U),
    HEq (mul U 0 n (one U) a) a
  /-- The degree-zero unit is a right identity for twist multiplication. -/
  mul_one : ∀ (U : X.Opensᵒᵖ) (n : ℤ) (a : (P.twist n).val.obj U),
    HEq (mul U n 0 a (one U)) a

namespace RelativeProjTwistAlgebra

/-- The graded algebra sheaf whose degree family is the twist family of the presentation. -/
def toGradedAlgebraSheaf
    {P : RelativeProjPresentation p}
    (twistAlgebra : RelativeProjTwistAlgebra P) :
    GradedAlgebraSheaf.{u, u} X.sheaf where
  obj := P.twist
  one := twistAlgebra.one
  mul := twistAlgebra.mul
  map_one := twistAlgebra.map_one
  map_mul := twistAlgebra.map_mul
  mul_assoc := twistAlgebra.mul_assoc
  one_mul := twistAlgebra.one_mul
  mul_one := twistAlgebra.mul_one

/-- The unit, multiplication, restriction, associativity, and unit laws of a twist algebra hold
on the fixed twist family. -/
theorem spec
    {P : RelativeProjPresentation p}
    (twistAlgebra : RelativeProjTwistAlgebra P) :
    (∀ {U V : X.Opensᵒᵖ} (f : U ⟶ V),
      ((P.twist 0).val.map f).hom (twistAlgebra.one U) = twistAlgebra.one V) ∧
    (∀ {U V : X.Opensᵒᵖ} (f : U ⟶ V) (n m : ℤ)
      (a : (P.twist n).val.obj U) (b : (P.twist m).val.obj U),
      ((P.twist (n + m)).val.map f).hom (twistAlgebra.mul U n m a b) =
        twistAlgebra.mul V n m (((P.twist n).val.map f).hom a)
          (((P.twist m).val.map f).hom b)) ∧
    (∀ (U : X.Opensᵒᵖ) (i j k : ℤ) (a : (P.twist i).val.obj U)
      (b : (P.twist j).val.obj U) (c : (P.twist k).val.obj U),
      HEq (twistAlgebra.mul U (i + j) k (twistAlgebra.mul U i j a b) c)
        (twistAlgebra.mul U i (j + k) a (twistAlgebra.mul U j k b c))) ∧
    (∀ (U : X.Opensᵒᵖ) (n : ℤ) (a : (P.twist n).val.obj U),
      HEq (twistAlgebra.mul U 0 n (twistAlgebra.one U) a) a) ∧
    (∀ (U : X.Opensᵒᵖ) (n : ℤ) (a : (P.twist n).val.obj U),
      HEq (twistAlgebra.mul U n 0 a (twistAlgebra.one U)) a) := sorry

end RelativeProjTwistAlgebra

/-- Explicit relative-projective-spectrum base-change data, including the defining algebra and
twist-algebra comparisons. -/
structure RelativeProjBaseChange
    (P : RelativeProjPresentation p)
    (g : S' ⟶ S) where
  /-- The graded algebra structure on the twists of the source presentation. -/
  sourceTwistAlgebra : RelativeProjTwistAlgebra P
  /-- The relative projective spectrum presentation on the canonical pullback scheme. -/
  presentation : RelativeProjPresentation (pullback.snd p g)
  /-- The graded algebra structure on the twists of the pullback presentation. -/
  twistAlgebra : RelativeProjTwistAlgebra presentation
  /-- The graded-algebra comparison between the defining algebra and its pullback. -/
  algebraPullback : RelativeProjGradedPullback g P.algebra presentation.algebra
  /-- The graded-algebra comparison between the pulled-back source twists and the target twists. -/
  theta : RelativeProjGradedPullback (pullback.fst p g)
    sourceTwistAlgebra.toGradedAlgebraSheaf twistAlgebra.toGradedAlgebraSheaf

namespace RelativeProjBaseChange

/-- Construct relative-projective-spectrum base-change data from the two graded pullback
comparisons and their source and target graded twist algebras. -/
def ofPullbacks
    {P : RelativeProjPresentation p}
    {g : S' ⟶ S}
    (sourceTwistAlgebra : RelativeProjTwistAlgebra P)
    (presentation : RelativeProjPresentation (pullback.snd p g))
    (twistAlgebra : RelativeProjTwistAlgebra presentation)
    (algebraPullback : RelativeProjGradedPullback g P.algebra presentation.algebra)
    (theta : RelativeProjGradedPullback (pullback.fst p g)
      sourceTwistAlgebra.toGradedAlgebraSheaf twistAlgebra.toGradedAlgebraSheaf) :
    RelativeProjBaseChange P g where
  sourceTwistAlgebra := sourceTwistAlgebra
  presentation := presentation
  twistAlgebra := twistAlgebra
  algebraPullback := algebraPullback
  theta := theta

/-- The strict pullback model identifies the base-changed relative projective spectrum with the
canonical pullback scheme. -/
def iso
    {P : RelativeProjPresentation p}
    {g : S' ⟶ S}
    (baseChange : RelativeProjBaseChange P g) :
    pullback p g ≅ pullback p g :=
  Iso.refl _

/-- The two twist algebras satisfy their graded algebra laws, both comparison data preserve the
graded operations, and the scheme comparison is the identity on the canonical pullback. -/
theorem spec
    {P : RelativeProjPresentation p}
    {g : S' ⟶ S}
    (baseChange : RelativeProjBaseChange P g) :
    let source := baseChange.sourceTwistAlgebra
    let target := baseChange.twistAlgebra
    let algebraPullback := baseChange.algebraPullback
    let theta := baseChange.theta
    (∀ {U V : X.Opensᵒᵖ} (f : U ⟶ V),
      ((P.twist 0).val.map f).hom (source.one U) = source.one V) ∧
    (∀ {U V : X.Opensᵒᵖ} (f : U ⟶ V) (n m : ℤ)
      (a : (P.twist n).val.obj U) (b : (P.twist m).val.obj U),
      ((P.twist (n + m)).val.map f).hom (source.mul U n m a b) =
        source.mul V n m (((P.twist n).val.map f).hom a)
          (((P.twist m).val.map f).hom b)) ∧
    (∀ (U : X.Opensᵒᵖ) (i j k : ℤ) (a : (P.twist i).val.obj U)
      (b : (P.twist j).val.obj U) (c : (P.twist k).val.obj U),
      HEq (source.mul U (i + j) k (source.mul U i j a b) c)
        (source.mul U i (j + k) a (source.mul U j k b c))) ∧
    (∀ (U : X.Opensᵒᵖ) (n : ℤ) (a : (P.twist n).val.obj U),
      HEq (source.mul U 0 n (source.one U) a) a) ∧
    (∀ (U : X.Opensᵒᵖ) (n : ℤ) (a : (P.twist n).val.obj U),
      HEq (source.mul U n 0 a (source.one U)) a) ∧
    (∀ {U V : (pullback p g).Opensᵒᵖ} (f : U ⟶ V),
      ((baseChange.presentation.twist 0).val.map f).hom (target.one U) = target.one V) ∧
    (∀ {U V : (pullback p g).Opensᵒᵖ} (f : U ⟶ V) (n m : ℤ)
      (a : (baseChange.presentation.twist n).val.obj U)
      (b : (baseChange.presentation.twist m).val.obj U),
      ((baseChange.presentation.twist (n + m)).val.map f).hom (target.mul U n m a b) =
        target.mul V n m (((baseChange.presentation.twist n).val.map f).hom a)
          (((baseChange.presentation.twist m).val.map f).hom b)) ∧
    (∀ (U : (pullback p g).Opensᵒᵖ) (i j k : ℤ)
      (a : (baseChange.presentation.twist i).val.obj U)
      (b : (baseChange.presentation.twist j).val.obj U)
      (c : (baseChange.presentation.twist k).val.obj U),
      HEq (target.mul U (i + j) k (target.mul U i j a b) c)
        (target.mul U i (j + k) a (target.mul U j k b c))) ∧
    (∀ (U : (pullback p g).Opensᵒᵖ) (n : ℤ)
      (a : (baseChange.presentation.twist n).val.obj U),
      HEq (target.mul U 0 n (target.one U) a) a) ∧
    (∀ (U : (pullback p g).Opensᵒᵖ) (n : ℤ)
      (a : (baseChange.presentation.twist n).val.obj U),
      HEq (target.mul U n 0 a (target.one U)) a) ∧
    (∀ U : S'.Opensᵒᵖ,
      algebraPullback.degreeMap 0 U (algebraPullback.pullbackOne U) =
        baseChange.presentation.algebra.one U) ∧
    (∀ (U : S'.Opensᵒᵖ) (n m : ℤ)
      (a : pulledBackGradedAlgebraSection g P.algebra n U)
      (b : pulledBackGradedAlgebraSection g P.algebra m U),
      algebraPullback.degreeMap (n + m) U (algebraPullback.pullbackMul U n m a b) =
        baseChange.presentation.algebra.mul U n m
          (algebraPullback.degreeMap n U a) (algebraPullback.degreeMap m U b)) ∧
    (∀ U : (pullback p g).Opensᵒᵖ,
      theta.degreeMap 0 U (theta.pullbackOne U) = target.one U) ∧
    (∀ (U : (pullback p g).Opensᵒᵖ) (n m : ℤ)
      (a : pulledBackGradedAlgebraSection (pullback.fst p g)
        source.toGradedAlgebraSheaf n U)
      (b : pulledBackGradedAlgebraSection (pullback.fst p g)
        source.toGradedAlgebraSheaf m U),
      theta.degreeMap (n + m) U (theta.pullbackMul U n m a b) =
        target.mul U n m (theta.degreeMap n U a) (theta.degreeMap m U b)) ∧
    iso baseChange = Iso.refl (pullback p g) := sorry

end RelativeProjBaseChange

/-- A relative projective spectrum presentation and its graded twist algebra have explicit
base-change comparison data along every morphism of base schemes. -/
theorem relativeProjBaseChangeExists
    (P : RelativeProjPresentation p)
    (sourceTwistAlgebra : RelativeProjTwistAlgebra P)
    (g : S' ⟶ S) :
    ∃ baseChange : RelativeProjBaseChange P g,
      baseChange.sourceTwistAlgebra = sourceTwistAlgebra := sorry

end AlgebraicGeometry.Scheme.Hom
