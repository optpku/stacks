module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Smooth.Basic
public import ReasLib.RingTheory.Smooth.Lifting
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ClassGroup
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Hyperelliptic
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

section
variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

/- Exercise 111.61.1 (Definitions) (1): a smooth algebra over `k` is a commutative `k`-algebra
which is formally smooth and of finite presentation. -/
@[stacks 0ELG] #check
  (Algebra.smooth_iff_finitePresentation_and_squareZeroLifting k A :
    Algebra.Smooth k A ↔ Algebra.FinitePresentation k A ∧
      (∀ ⦃B : Type (max u u)⦄ [CommRing B] [Algebra k B] (I : Ideal B),
        I ^ 2 = ⊥ →
          Function.Surjective
            ((Ideal.Quotient.mkₐ k I).comp : (A →ₐ[k] B) → A →ₐ[k] B ⧸ I)))

#check (Algebra.Smooth k A : Prop)

#check (Algebra.FormallySmooth k A : Prop)

#check (Algebra.FinitePresentation k A : Prop)

#check Algebra.smooth_iff

end

section
variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [Curve X] [Projective X.hom]
variable (L : X.left.Modules) [Scheme.Modules.Invertible L]

/- Exercise 111.61.1 (Definitions) (2): the degree of an invertible `𝒪_X`-module `L` on a
projective curve `X` is `χ(X, L) - χ(X, 𝒪_X)`. The canonical definition applies to proper
curves, and hence to the projective curves in the exercise. -/
@[stacks 0ELG] #check (AlgebraicGeometry.Scheme.Modules.curveDegreeOfInvertible X.hom
    (topologicalKrullDim_eq_one X).le L : ℤ)

#check Scheme.Modules.curveDegree

#check Scheme.Modules.curveDegree_def

#check Scheme.Modules.curveDegreeOfInvertible_eq_eulerCharacteristic_sub_structureSheaf

end

section
variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [Curve X] [Projective X.hom]

/- Exercise 111.61.1 (Definitions) (3): the genus of a projective curve `X` over `k` is
`dim_k H¹(X, 𝒪_X)`. -/
@[stacks 0ELG] #check (AlgebraicGeometry.SchemeOverField.genusOfCurve X : ℕ)

#check (AlgebraicGeometry.SchemeOverField.genusOfCurve_def X :
  SchemeOverField.genusOfCurve X = Scheme.Hom.cohomologyFinrank X.hom
    (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1)

end

section
variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [Curve X] [Projective X.hom]

/- Exercise 111.61.1 (Definitions) (4): the Weil divisor class group of the projective curve
`X` is `Div(X.left) ⧸ Prin(X.left)`. -/
@[stacks 0ELG] #check (AlgebraicGeometry.Curve.classGroup X : Type u)

end

section
variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [Curve X] [Projective X.hom]

/- Exercise 111.61.1 (Definitions) (5): a proper curve `X` is hyperelliptic when it admits a
linear series of degree `2` and dimension `1` (a `g¹₂`). -/
@[stacks 0ELG] #check (AlgebraicGeometry.Curve.IsHyperelliptic X : Prop)

#check LinearSeries

#check (LinearSeries X (topologicalKrullDim_eq_one X).le 2 1)

#check (Curve.isHyperelliptic_iff X)

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (S : SchemeOverField k) [Projective S.hom] [Smooth S.hom] [IsIntegral S.left]
variable (hSdim : topologicalKrullDim S.left = 2)
variable (C D : S.left.IdealSheafData)
variable [IsIntegral C.subscheme] [IsIntegral D.subscheme]
variable (hCdim : topologicalKrullDim C.subscheme = 1)
variable (hDdim : topologicalKrullDim D.subscheme = 1)

/- Exercise 111.61.1 (Definitions) (6): for two integral curves `C`, `D` on an integral
smooth projective surface `S` over `k`, the intersection number `C · D` is the intersection
coefficient on `D` of the line bundle associated to `C`. -/
@[stacks 0ELG] #check
  (AlgebraicGeometry.Scheme.Modules.Intersection.curveNumber S hSdim C D hCdim hDdim : ℚ)

#check AlgebraicGeometry.Scheme.Modules.Intersection.number_eq_coeff

#check
  (AlgebraicGeometry.Scheme.Modules.Intersection.lineNumber :
    ∀ (k : Type u) [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (Z : X.IdealSheafData)
      [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
      (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L],
      ℚ)

#check
  (AlgebraicGeometry.Scheme.Modules.Intersection.selfNumber :
    ∀ (k : Type u) [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (Z : X.IdealSheafData) {d : ℕ},
      topologicalKrullDim Z.subscheme = d →
      ∀ [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
        (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L], ℚ)

end
