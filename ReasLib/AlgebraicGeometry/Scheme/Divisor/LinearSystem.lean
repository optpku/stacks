module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.VectorSpace
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.CurveDegree
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.LinearEquivalence
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.AbelMap
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Components
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Hilbert.SmoothProperCurve

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The complete linear system of an effective Cartier divisor is the set of effective Cartier
divisors linearly equivalent to it. -/
def completeLinearSystem
    (X : Scheme.{u}) (D : X.IdealSheafData)
    [hD : IsEffectiveCartierDivisor D.subschemeι] : Set X.IdealSheafData :=
  {E | ∃ hE : IsEffectiveCartierDivisor E.subschemeι,
    @linearlyEquivalent X D E hD hE}

/-- Membership in the complete linear system is effective-Cartierness together with linear
equivalence to the fixed divisor. -/
theorem completeLinearSystem_def
    (X : Scheme.{u}) (D E : X.IdealSheafData)
    [hD : IsEffectiveCartierDivisor D.subschemeι] :
    E ∈ completeLinearSystem X D ↔
      ∃ hE : IsEffectiveCartierDivisor E.subschemeι,
        @linearlyEquivalent X D E hD hE := sorry

namespace CompleteLinearSystem

/-- The Picard class of a degree-`d` effective Cartier divisor belongs to the degree-`d`
component of the Picard group. -/
theorem picardClass_mem_degreeClasses
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] (d : ℕ)
    (degree_eq : Scheme.Modules.curveDegreeOfInvertible X.hom
      (topologicalKrullDim_eq_one X).le D.associatedSheaf = (d : ℤ)) :
    Scheme.Modules.picardClass D.associatedSheaf ∈
      RelativePicard.degreeClasses X (d : ℤ) := sorry

/-- The `k`-point of the degree-`d` Picard component represented by `𝒪_X(D)`. -/
def picardPoint
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] (d : ℕ)
    (degree_eq : Scheme.Modules.curveDegreeOfInvertible X.hom
      (topologicalKrullDim_eq_one X).le D.associatedSheaf = (d : ℤ)) :
    (𝟙_ (SchemeOverField k)) ⟶ RelativePicard.component X (d : ℤ) :=
  RelativePicard.degreeClassToComponentPoint X (d : ℤ)
    ⟨Scheme.Modules.picardClass D.associatedSheaf,
      picardClass_mem_degreeClasses X D d degree_eq⟩

/-- The Picard point of `D` is obtained from its degree-`d` Picard class. -/
theorem picardPoint_def
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] (d : ℕ)
    (degree_eq : Scheme.Modules.curveDegreeOfInvertible X.hom
      (topologicalKrullDim_eq_one X).le D.associatedSheaf = (d : ℤ)) :
    picardPoint X D d degree_eq =
      RelativePicard.degreeClassToComponentPoint X (d : ℤ)
        ⟨Scheme.Modules.picardClass D.associatedSheaf,
          picardClass_mem_degreeClasses X D d degree_eq⟩ := sorry

/-- The scheme-theoretic Abel fibre over the Picard point represented by `𝒪_X(D)`. -/
def abelFibre
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] (d : ℕ)
    (degree_eq : Scheme.Modules.curveDegreeOfInvertible X.hom
      (topologicalKrullDim_eq_one X).le D.associatedSheaf = (d : ℤ)) :
    SchemeOverField k :=
  pullback (RelativePicard.abelMap X d) (picardPoint X D d degree_eq)

/-- The Abel fibre unfolds to the pullback of the Abel map along the divisor's Picard point. -/
theorem abelFibre_def
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] (d : ℕ)
    (degree_eq : Scheme.Modules.curveDegreeOfInvertible X.hom
      (topologicalKrullDim_eq_one X).le D.associatedSheaf = (d : ℤ)) :
    abelFibre X D d degree_eq =
      pullback (RelativePicard.abelMap X d) (picardPoint X D d degree_eq) := sorry

/-- The canonical scheme owner for the complete linear system, presented as the projective
scheme of the dual section space. -/
def scheme
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] : SchemeOverField k :=
  Over.mk (ProjectiveSpace.VectorSpace.toSpec k
    (Module.Dual k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf)))

/-- The complete-linear-system scheme is the projective scheme of the dual section space. -/
theorem scheme_def
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] :
    scheme X D = Over.mk (ProjectiveSpace.VectorSpace.toSpec k
      (Module.Dual k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf))) := sorry

/-- Global sections of the line bundle of an effective divisor on a projective curve form a
finite-dimensional vector space over the base field. -/
theorem associatedSheafSections_finiteDimensional
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] :
    FiniteDimensional k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf) := sorry

/-- The numerical projective-space index of the complete linear system presentation. -/
def projectiveIndex
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] : ℕ :=
  Module.finrank k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf) - 1

/-- The projective-space index is one less than the dimension of the section space. -/
theorem projectiveIndex_def
    {k : Type u} [Field k] (X : SchemeOverField k)
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] :
    projectiveIndex X D =
      Module.finrank k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf) - 1 := sorry

/-- The effective divisors in a complete system are exactly the rational Hilbert points in its
Abel-map fibre. -/
theorem points_iff
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D E : X.left.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    [IsEffectiveCartierDivisor E.subschemeι] (d : ℕ)
    (degree_eq : Scheme.Modules.curveDegreeOfInvertible X.hom
      (topologicalKrullDim_eq_one X).le D.associatedSheaf = (d : ℤ)) :
    E ∈ completeLinearSystem X.left D ↔
      ∃ p : (Over.mk (FieldExtension.specMap k k) : SchemeOverField k) ⟶
          abelFibre X D d degree_eq,
        (Hilbert.rationalPointsEquiv X d
          (p ≫ pullback.fst (RelativePicard.abelMap X d)
            (picardPoint X D d degree_eq))).ideal =
          E.comap (pullback.fst X.hom (FieldExtension.specMap k k)) := sorry

/-- The complete-system scheme is canonically identified with the projective model of the
dual section space. -/
theorem abelFibre_iso_scheme
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] (d : ℕ)
    (degree_eq : Scheme.Modules.curveDegreeOfInvertible X.hom
      (topologicalKrullDim_eq_one X).le D.associatedSheaf = (d : ℤ)) :
    Nonempty (abelFibre X D d degree_eq ≅ scheme X D) := sorry

/-- If the complete-system scheme has dimension `m`, then its section space has dimension
`m + 1`. -/
theorem dimension_add_one
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (m : ℕ) (h_scheme_dim : topologicalKrullDim (scheme X D).left = m) :
    m + 1 = Module.finrank k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf) := sorry

/-- The complete-system scheme is isomorphic to projective `m`-space when the section space has
dimension `m + 1`. -/
theorem scheme_iso_projectiveSpace
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [AlgebraicGeometry.Curve X] [Smooth X.hom] [Projective X.hom]
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (m : ℕ)
    (hdim : Module.finrank k (Scheme.Hom.globalSectionsMod X.hom D.associatedSheaf) = m + 1) :
    Nonempty (scheme X D ≅ Over.mk (ProjectiveSpace.toSpec k m)) := sorry

end CompleteLinearSystem

end AlgebraicGeometry.Scheme.IdealSheafData
