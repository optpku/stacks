/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.GradedPullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullbacks of affine tilde graded algebras

This module identifies homogeneous elements of a graded algebra with their
canonical sections in a degreewise pullback of its affine tilde algebra.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

namespace PullbackTilde

/-- Comparison data between the degreewise pullback of the affine tilde algebra associated to a
graded algebra and a graded algebra sheaf on the source scheme.  Its homogeneous sections are the
canonical affine sections transported through the two comparisons. -/
@[stacks 0897 "pullback-tilde graded algebra comparison"]
structure Comparison
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (pullbackTildeB : GradedAlgebraSheaf.{u, u} X.sheaf) where
  /-- The affine graded algebra sheaf whose degree pieces model the homogeneous pieces of the
  graded algebra. -/
  tildeB : GradedAlgebraSheaf.{u, u} (Spec (CommRingCat.of A)).sheaf
  /-- The degreewise affine-tilde identifications. -/
  degreeIso : ∀ n : ℕ,
    ((tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A (𝒜 n))) ≅ tildeB.obj (n : ℤ)
  /-- Every negative-degree piece of the integer-graded affine model is zero. -/
  negativeDegreeIsZero : ∀ n : ℤ, n < 0 → IsZero (tildeB.obj n)
  /-- The degreewise identification of the chosen algebra sheaf with the pullback of the affine
  model. -/
  pullbackIso : Scheme.RelativeProjGradedPullback f tildeB pullbackTildeB
  /-- The canonical homogeneous elements, bundled as additive maps into compatible sections. -/
  homogeneousSection : ∀ n : ℕ,
    𝒜 n →+ (pullbackTildeB.obj (n : ℤ)).val.obj (Opposite.op ⊤)
  /-- A homogeneous section is obtained from the affine tilde section, transported to the affine
  model, pulled back along the scheme morphism, and transported to the chosen algebra sheaf. -/
  homogeneousSection_eq : ∀ (n : ℕ) (b : 𝒜 n),
    homogeneousSection n b =
      (SheafOfModules.sectionsMap (pullbackIso.degreeIso (n : ℤ)).hom
        (Scheme.Modules.sectionsPullback f (tildeB.obj (n : ℤ))
          (SheafOfModules.sectionsMap (degreeIso n).hom
            (RingedSpace.sectionFromTop
              ((tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A (𝒜 n)))
              ((tilde.isoTop
                (R := CommRingCat.of A) (ModuleCat.of (CommRingCat.of A) (𝒜 n))).hom b))))).1
        (Opposite.op ⊤)
  /-- The homogeneous unit is the unit section of the chosen graded algebra sheaf. -/
  homogeneousSection_one :
    homogeneousSection 0
        (@GradedMonoid.GOne.one ℕ (fun n ↦ 𝒜 n) _ _) =
      pullbackTildeB.one (Opposite.op ⊤)
  /-- The canonical homogeneous sections preserve graded multiplication. -/
  homogeneousSection_mul : ∀ (m n : ℕ) (a : 𝒜 m) (b : 𝒜 n),
    HEq (homogeneousSection (m + n)
        (@GradedMonoid.GMul.mul ℕ (fun n ↦ 𝒜 n) _ _ m n a b))
      (pullbackTildeB.mul (Opposite.op ⊤) (m : ℤ) (n : ℤ)
        (homogeneousSection m a) (homogeneousSection n b))

namespace Comparison

/-- Constructs a comparison from an affine graded model, degree identifications, a pullback
comparison, and compatible homogeneous sections. -/
@[stacks 0897 "constructor for a pullback-tilde graded algebra comparison"]
def ofComponents
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (pullbackTildeB : GradedAlgebraSheaf.{u, u} X.sheaf)
    (tildeB : GradedAlgebraSheaf.{u, u} (Spec (CommRingCat.of A)).sheaf)
    (degreeIso : ∀ n : ℕ,
      ((tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A (𝒜 n))) ≅ tildeB.obj (n : ℤ))
    (pullbackIso : Scheme.RelativeProjGradedPullback f tildeB pullbackTildeB)
    (homogeneousSection : ∀ n : ℕ,
      𝒜 n →+ (pullbackTildeB.obj (n : ℤ)).val.obj (Opposite.op ⊤))
    (negativeDegreeIsZero : ∀ n : ℤ, n < 0 → IsZero (tildeB.obj n))
    (homogeneousSection_eq : ∀ (n : ℕ) (b : 𝒜 n),
      homogeneousSection n b =
        (SheafOfModules.sectionsMap (pullbackIso.degreeIso (n : ℤ)).hom
          (Scheme.Modules.sectionsPullback f (tildeB.obj (n : ℤ))
            (SheafOfModules.sectionsMap (degreeIso n).hom
              (RingedSpace.sectionFromTop
                ((tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A (𝒜 n)))
                ((tilde.isoTop
                  (R := CommRingCat.of A) (ModuleCat.of (CommRingCat.of A) (𝒜 n))).hom b))))).1
          (Opposite.op ⊤))
    (homogeneousSection_one :
      homogeneousSection 0
          (@GradedMonoid.GOne.one ℕ (fun n ↦ 𝒜 n) _ _) =
        pullbackTildeB.one (Opposite.op ⊤))
    (homogeneousSection_mul : ∀ (m n : ℕ) (a : 𝒜 m) (b : 𝒜 n),
      HEq (homogeneousSection (m + n)
          (@GradedMonoid.GMul.mul ℕ (fun n ↦ 𝒜 n) _ _ m n a b))
        (pullbackTildeB.mul (Opposite.op ⊤) (m : ℤ) (n : ℤ)
          (homogeneousSection m a) (homogeneousSection n b))) :
    Comparison 𝒜 f pullbackTildeB :=
  { tildeB := tildeB
    degreeIso := degreeIso
    negativeDegreeIsZero := negativeDegreeIsZero
    pullbackIso := pullbackIso
    homogeneousSection := homogeneousSection
    homogeneousSection_eq := homogeneousSection_eq
    homogeneousSection_one := homogeneousSection_one
    homogeneousSection_mul := homogeneousSection_mul }

/-- The degreewise pullback comparison underlying an affine-tilde graded algebra comparison. -/
@[stacks 0897 "underlying graded pullback comparison"]
def toGradedPullback
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {𝒜 : ℕ → Submodule A B} [GradedAlgebra 𝒜]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of A)}
    {pullbackTildeB : GradedAlgebraSheaf.{u, u} X.sheaf}
    (pullbackData : Comparison 𝒜 f pullbackTildeB) :
    Scheme.RelativeProjGradedPullback f pullbackData.tildeB pullbackTildeB :=
  pullbackData.pullbackIso

/-- The pullback-tilde comparison simultaneously specifies negative-degree vanishing, its
canonical homogeneous sections, their unit and multiplication laws, and the algebra laws of the
degreewise pullback. -/
@[stacks 0897 "specification of the pullback-tilde graded algebra comparison"]
theorem spec
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    {pullbackTildeB : GradedAlgebraSheaf.{u, u} X.sheaf}
    (pullbackData : Comparison 𝒜 f pullbackTildeB) :
    (∀ n : ℤ, n < 0 → IsZero (pullbackData.tildeB.obj n)) ∧
    (∀ (n : ℕ) (b : 𝒜 n),
      pullbackData.homogeneousSection n b =
        (SheafOfModules.sectionsMap (pullbackData.pullbackIso.degreeIso (n : ℤ)).hom
          (Scheme.Modules.sectionsPullback f (pullbackData.tildeB.obj (n : ℤ))
            (SheafOfModules.sectionsMap (pullbackData.degreeIso n).hom
              (RingedSpace.sectionFromTop
                ((tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A (𝒜 n)))
                ((tilde.isoTop
                  (R := CommRingCat.of A)
                  (ModuleCat.of (CommRingCat.of A) (𝒜 n))).hom b))))).1
          (Opposite.op ⊤)) ∧
    (pullbackData.homogeneousSection 0
        (@GradedMonoid.GOne.one ℕ (fun n ↦ 𝒜 n) _ _) =
      pullbackTildeB.one (Opposite.op ⊤)) ∧
    (∀ (m n : ℕ) (a : 𝒜 m) (b : 𝒜 n),
      HEq (pullbackData.homogeneousSection (m + n)
          (@GradedMonoid.GMul.mul ℕ (fun n ↦ 𝒜 n) _ _ m n a b))
        (pullbackTildeB.mul (Opposite.op ⊤) (m : ℤ) (n : ℤ)
          (pullbackData.homogeneousSection m a)
          (pullbackData.homogeneousSection n b))) ∧
    ((∀ U : (X.Opens)ᵒᵖ,
        pullbackData.pullbackIso.degreeMap 0 U
            (pullbackData.pullbackIso.pullbackOne U) = pullbackTildeB.one U) ∧
      (∀ (U : (X.Opens)ᵒᵖ) (n m : ℤ)
        (a : Scheme.pulledBackGradedAlgebraSection
          f pullbackData.tildeB n U)
        (b : Scheme.pulledBackGradedAlgebraSection
          f pullbackData.tildeB m U),
        pullbackData.pullbackIso.degreeMap (n + m) U
            (pullbackData.pullbackIso.pullbackMul U n m a b) =
          pullbackTildeB.mul U n m
            (pullbackData.pullbackIso.degreeMap n U a)
            (pullbackData.pullbackIso.degreeMap m U b))) := sorry

end Comparison

end PullbackTilde

end AlgebraicGeometry.Scheme.Modules
