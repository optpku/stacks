/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardEtale
public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous
public import stacks_project.Chap07.Definition_7_6_2_Site
public import stacks_project.Chap66.Definition_66_18_1_Site

/-!
# Affine étale site of an algebraic space

The affine étale site of an algebraic space `X` is the full subcategory of the small étale
site on objects whose source scheme is affine, with covering families those that cover in
`X_étale` and generate the same sieve on schemes as a finite standard étale cover.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The object property selecting affine source schemes in the small étale site of `X`. -/
def affineEtaleObjects {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ObjectProperty (smallEtaleSite X) :=
  fun U ↦ IsAffine U.left.left

/-- An object of the small étale site of `X` is affine if and only if its source scheme is
affine. -/
theorem mem_affineEtaleObjects_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : smallEtaleSite X} : affineEtaleObjects X U ↔ IsAffine U.left.left :=
  Iff.rfl

/-- The affine étale site of an algebraic space `X` is the full subcategory of `X_étale` on
affine source schemes. -/
abbrev affineEtaleSite {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  (affineEtaleObjects X).FullSubcategory

/-- Construct an object of the affine étale site of `X` from an étale morphism of an affine
scheme over `S` into `X`. -/
def affineEtaleSite.mk {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} [IsAffine U.left]
    (φ : ofOver U ⟶ X) [Etale φ] : affineEtaleSite X where
  obj := MorphismProperty.CostructuredArrow.mk ⊤ φ ‹_›
  property := ‹IsAffine U.left›

/-- The underlying object of `affineEtaleSite.mk φ` is `smallEtaleSite.mk φ`. -/
@[simp]
theorem affineEtaleSite.mk_obj {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ] :
    (affineEtaleSite.mk φ).obj = smallEtaleSite.mk φ :=
  rfl

/-- The underlying scheme over `S` of `affineEtaleSite.mk φ` is the domain of `φ`. -/
@[simp]
theorem affineEtaleSite.mk_left {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ] :
    (affineEtaleSite.mk φ).obj.left = U :=
  rfl

/-- Every object of the affine étale site of `X` has affine source scheme. -/
instance affineEtaleSite_obj_isAffine {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : affineEtaleSite X) : IsAffine U.obj.left.left :=
  U.property

/-- The inclusion functor from the affine étale site of `X` to the small étale site of `X`. -/
def affineEtaleInclusion {S : Scheme.{u}} (X : AlgebraicSpace S) :
    affineEtaleSite X ⥤ smallEtaleSite X :=
  (affineEtaleObjects X).ι

/-- `affineEtaleInclusion X` is the full-subcategory inclusion of affine objects. -/
theorem affineEtaleInclusion_def {S : Scheme.{u}} (X : AlgebraicSpace S) :
    affineEtaleInclusion X = (affineEtaleObjects X).ι :=
  rfl

/-- On objects, `affineEtaleInclusion X` is the identity on the underlying étale object. -/
@[simp]
theorem affineEtaleInclusion_obj {S : Scheme.{u}} {X : AlgebraicSpace S} (U : affineEtaleSite X) :
    (affineEtaleInclusion X).obj U = U.obj :=
  rfl

/-- On morphisms, `affineEtaleInclusion X` is the identity on the underlying étale morphism. -/
@[simp]
theorem affineEtaleInclusion_map {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V : affineEtaleSite X} (f : U ⟶ V) : (affineEtaleInclusion X).map f = f.hom :=
  rfl

/-- The forgetful functor from the affine étale site of `X` to schemes. -/
abbrev affineEtaleToScheme {S : Scheme.{u}} (X : AlgebraicSpace S) :
    affineEtaleSite X ⥤ Scheme :=
  affineEtaleInclusion X ⋙ smallEtaleToScheme X

/-- A finite standard étale cover of an affine object of the small étale site of `X`. -/
abbrev AffineEtaleStandardCover {S : Scheme.{u}} {X : AlgebraicSpace S} (U : affineEtaleSite X) :=
  @StandardEtaleCover ((affineEtaleToScheme X).obj U) U.property

/-- A presieve on the affine étale site of `X` is a covering when it covers in `X_étale` and
its image in schemes generates the same sieve as a finite standard étale cover. -/
def affineEtaleCovering {S : Scheme.{u}} (X : AlgebraicSpace S) {U : affineEtaleSite X}
    (R : Presieve U) : Prop :=
  R.map (affineEtaleInclusion X) ∈ smallEtalePrecoverage X U.obj ∧
    ∃ 𝒰 : AffineEtaleStandardCover U,
      Sieve.generate (R.map (affineEtaleToScheme X)) =
        Sieve.generate (Presieve.ofArrows
          (@StandardEtaleCover.U _ U.property 𝒰)
          (@StandardEtaleCover.map _ U.property 𝒰))

/-- The precoverage of ambient-covering finite standard étale families on the affine étale
site of `X`. -/
def affineEtalePrecoverage {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Precoverage (affineEtaleSite X) where
  coverings := fun _ ↦ { R | affineEtaleCovering X R }

/-- Membership in the affine étale precoverage of `X` records both ambient covering and
equality of generated sieves with a finite standard étale cover. -/
theorem mem_affineEtalePrecoverage_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : affineEtaleSite X} {R : Presieve U} :
    R ∈ affineEtalePrecoverage X U ↔
      R.map (affineEtaleInclusion X) ∈ smallEtalePrecoverage X U.obj ∧
        ∃ 𝒰 : AffineEtaleStandardCover U,
          Sieve.generate (R.map (affineEtaleToScheme X)) =
            Sieve.generate (Presieve.ofArrows
              (@StandardEtaleCover.U _ U.property 𝒰)
              (@StandardEtaleCover.map _ U.property 𝒰)) :=
  Iff.rfl

/-- A displayed family covers in the affine étale precoverage of `X` if and only if its image
covers in `X_étale` and generates the same sieve on schemes as a finite standard étale cover. -/
theorem ofArrows_mem_affineEtalePrecoverage_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} {U : affineEtaleSite X} {V : ι → affineEtaleSite X} {f : ∀ i, V i ⟶ U} :
    Presieve.ofArrows V f ∈ affineEtalePrecoverage X U ↔
      Presieve.ofArrows (fun i ↦ (affineEtaleInclusion X).obj (V i))
          (fun i ↦ (affineEtaleInclusion X).map (f i)) ∈
        smallEtalePrecoverage X U.obj ∧
        ∃ 𝒰 : AffineEtaleStandardCover U,
          Sieve.generate (Presieve.ofArrows (fun i ↦ (affineEtaleToScheme X).obj (V i))
              (fun i ↦ (affineEtaleToScheme X).map (f i))) =
            Sieve.generate (Presieve.ofArrows
              (@StandardEtaleCover.U _ U.property 𝒰)
              (@StandardEtaleCover.map _ U.property 𝒰)) :=
  sorry

/-- The affine étale topology of an algebraic space `X` is the Grothendieck topology generated
by finite standard étale covering families. -/
def affineEtaleTopology {S : Scheme.{u}} (X : AlgebraicSpace S) :
    GrothendieckTopology (affineEtaleSite X) :=
  (affineEtalePrecoverage X).toGrothendieck

/-- The affine étale topology of `X` is generated by its affine étale precoverage. -/
theorem affineEtaleTopology_def {S : Scheme.{u}} (X : AlgebraicSpace S) :
    affineEtaleTopology X = (affineEtalePrecoverage X).toGrothendieck :=
  rfl

/-- The standard étale covering families of affine schemes over an algebraic space satisfy the
site axioms. -/
instance affineEtalePrecoverage.instIsSite {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineEtalePrecoverage X).IsSite :=
  sorry

/-- The opposite of the affine étale inclusion has pointwise right Kan extensions on sheaves of
types in universe `u + 1`. -/
instance affineEtaleInclusion_op_hasPointwiseRightKanExtension {S : Scheme.{u}}
    (X : AlgebraicSpace S) (P : (affineEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    (affineEtaleInclusion X).op.HasPointwiseRightKanExtension P :=
  sorry


end AlgebraicGeometry.AlgebraicSpace
