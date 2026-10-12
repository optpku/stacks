/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.RationalCohomology
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.FirstChern
public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Pullback
public import ReasLib.AlgebraicGeometry.ChernClass.ChernCharacter
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.Rational

/-- The rational relative de Rham first Chern class of a Picard class is the class of its
canonical logarithmic representative. -/
def firstChernClass (X : SchemeOverField (ULift.{u} ℚ)) (L : X.left.PicardGroup) :
    evenCohomology X 1 :=
  ClassRepresentative.inverse X.hom 2
    (FirstChern.logarithmicRepresentative X.hom (LogarithmicForms.firstChernHom X.hom L))

/-- The exponential of a rational first Chern class has inverse-factorial-normalized
canonical cup powers as its completed even cohomology components. -/
def expFirstChern (X : SchemeOverField (ULift.{u} ℚ)) (L : X.left.PicardGroup) :
    CompletedEven X :=
  fun degree ↦ (baseRingMapOfAffineTarget X.hom).hom
    (ULift.up ((degree.factorial : ℚ)⁻¹)) •
      CanonicalAction.evenPower X.hom (firstChernClass X L) degree

/-- The degree-`degree` component of the first-Chern exponential is its cup power divided
by `degree.factorial`. -/
theorem expFirstChern_apply (X : SchemeOverField (ULift.{u} ℚ))
    (L : X.left.PicardGroup) (degree : ℕ) :
    expFirstChern X L degree = (baseRingMapOfAffineTarget X.hom).hom
      (ULift.up ((degree.factorial : ℚ)⁻¹)) •
        CanonicalAction.evenPower X.hom (firstChernClass X L) degree := sorry

/-- The full subcategory of schemes over `ℚ` whose underlying spaces are quasi-compact
and quasi-separated. -/
abbrev QcqsScheme :=
  ObjectProperty.FullSubcategory (fun X : SchemeOverField (ULift.{u} ℚ) ↦
    CompactSpace X.left ∧ QuasiSeparatedSpace X.left)

/-- A family of rational de Rham character ring maps is natural when it commutes with
pullback along every morphism of quasi-compact, quasi-separated schemes over `ℚ`. -/
def IsNatural
    (ch : ∀ X : QcqsScheme.{u}, VectorBundleK0 X.obj.left →+* CompletedEven X.obj) : Prop :=
  ∀ {X' X : QcqsScheme.{u}} (f : X' ⟶ X) (α : VectorBundleK0 X.obj.left),
    pullback f.hom (ch X α) = ch X' (VectorBundleK0.pullback f.hom.left α)

/-- A family of rational de Rham character ring maps is normalized on line bundles when
every Picard class maps to the exponential of its canonical first Chern class. -/
def LineBundleNormalized
    (ch : ∀ X : QcqsScheme.{u}, VectorBundleK0 X.obj.left →+* CompletedEven X.obj) : Prop :=
  ∀ (X : QcqsScheme.{u}) (L : X.obj.left.PicardGroup),
    ch X (ChernClass.picardK0Class X.obj.left L) = expFirstChern X.obj L

/-- There is a unique family of Chern-character ring maps from vector-bundle `K₀` to
completed even relative de Rham cohomology on quasi-compact, quasi-separated schemes
over `ℚ`, natural under pullback and normalized by the first-Chern exponential. -/
theorem existsUniqueChernCharacter :
    ∃! ch : ∀ X : QcqsScheme.{u}, VectorBundleK0 X.obj.left →+* CompletedEven X.obj,
      IsNatural ch ∧ LineBundleNormalized ch := sorry

end AlgebraicGeometry.Scheme.DeRham.Rational
