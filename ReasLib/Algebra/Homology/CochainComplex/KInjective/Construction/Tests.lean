module

public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Construction

/-! # Nullhomotopies for the coded K-injective tests

The native factorization provides the lift of each test map across its identity-cone inclusion.
Composing that lift with the native cone contraction gives the actual homotopy components.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

namespace CochainComplex.KInjectiveResolution.Construction

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

attribute [local instance] Abelian.hasFiniteBiproducts

/-- The actual second arrow from the same small-object factorization. -/
def replacementProjection (K : CochainComplex C ℤ) :
    (replacement C).obj K ⟶ (HomologicalComplex.zero : CochainComplex C ℤ) :=
  (factorization C).p.app ((zeroArrow C).obj K)

/-- Each coded identity-cone inclusion lifts against the replacement projection. -/
instance testInclusion_rlp (K : CochainComplex C ℤ) (c : TestCode C) :
    HasLiftingProperty (testInclusion C c) (replacementProjection C K) :=
  (factorization C).hp ((zeroArrow C).obj K) _
    (MorphismProperty.ofHoms.mk (Sum.inl c))

/-- The square whose top arrow is the specified test morphism and whose bottom is zero. -/
theorem testConeSquare (K : CochainComplex C ℤ) (c : TestCode C)
    (f : testComplex C c ⟶ (replacement C).obj K) :
    CommSq f (testInclusion C c) (replacementProjection C K) 0 :=
  ⟨(HomologicalComplex.isZero_zero (V := C) (c := ComplexShape.up ℤ)).eq_of_tgt _ _⟩

/-- The native small-object lift extends the specified map across its identity cone. -/
def testConeExtension (K : CochainComplex C ℤ) (c : TestCode C)
    (f : testComplex C c ⟶ (replacement C).obj K) :
    testCone C c ⟶ (replacement C).obj K :=
  (testConeSquare C K c f).lift

/-- The extension restricts to the original test morphism. -/
@[reassoc (attr := simp)]
lemma testInclusion_testConeExtension (K : CochainComplex C ℤ) (c : TestCode C)
    (f : testComplex C c ⟶ (replacement C).obj K) :
    testInclusion C c ≫ testConeExtension C K c f = f :=
  (testConeSquare C K c f).fac_left

set_option backward.isDefEq.respectTransparency false in
/-- The identity-cone inclusion has its native explicit nullhomotopy. -/
def testInclusionHomotopy (c : TestCode C) : Homotopy (testInclusion C c) 0 := by
  simpa only [Category.id_comp, testInclusion, mappingCone.inr] using
    HomologicalComplex.homotopyCofiber.inrCompHomotopy (𝟙 (testComplex C c))
      (fun j ↦ ⟨j - 1, by change j - 1 + 1 = j; omega⟩)

set_option backward.isDefEq.respectTransparency false in
/-- Compose the explicit cone contraction with its actual lift to kill a coded test map. -/
def testNullHomotopy (K : CochainComplex C ℤ) (c : TestCode C)
    (f : testComplex C c ⟶ (replacement C).obj K) : Homotopy f 0 :=
  (Homotopy.ofEq (testInclusion_testConeExtension C K c f).symm).trans
    (((testInclusionHomotopy C c).compRight (testConeExtension C K c f)).trans
      (Homotopy.ofEq (by simp)))

set_option backward.isDefEq.respectTransparency false in
/-- Each component is the cone contraction followed by the actual extension component. -/
@[simp]
lemma testNullHomotopy_hom (K : CochainComplex C ℤ) (c : TestCode C)
    (f : testComplex C c ⟶ (replacement C).obj K) (p q : ℤ) :
    (testNullHomotopy C K c f).hom p q =
      (testInclusionHomotopy C c).hom p q ≫ (testConeExtension C K c f).f q := by
  simp only [testNullHomotopy, Homotopy.trans, Homotopy.ofEq, Homotopy.compRight,
    zero_add, add_zero]

end CochainComplex.KInjectiveResolution.Construction
