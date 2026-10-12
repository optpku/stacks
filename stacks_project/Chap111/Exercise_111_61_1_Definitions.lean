/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ClassGroup
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Number
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Genus
public import stacks_project.Chap111.Exercise_111_66_7_Hyperelliptic
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
@[stacks 0ELG] #check (Algebra.Smooth k A : Prop)

#check (Algebra.FormallySmooth k A : Prop)

#check (Algebra.FinitePresentation k A : Prop)

#check Algebra.smooth_iff

end

section
variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [Curve X] [Projective X.hom]
variable (L : X.left.Modules) [Scheme.Modules.Invertible L]

/- Exercise 111.61.1 (Definitions) (2): the degree of an invertible `𝒪_X`-module `L` on a
projective curve `X` is `χ(X, L) - χ(X, 𝒪_X)`. -/
@[stacks 0ELG] #check (Scheme.Modules.curveDegreeOfInvertible X.hom
    (topologicalKrullDim_eq_one X).le L : ℤ)

#check Scheme.Modules.curveDegree

#check Scheme.Modules.curveDegree_def

#check Scheme.Modules.curveDegreeOfInvertible_eq_eulerCharacteristic_sub_structureSheaf

end

section
variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [Curve X] [Projective X.hom]
variable (h_dimension : topologicalKrullDim X.left = 1)
variable (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))

/- Exercise 111.61.1 (Definitions) (3): the genus of a projective curve `X` over `k` is
`dim_k H¹(X, 𝒪_X)`, the Stacks 0BY7 arithmetic genus of a proper one-dimensional scheme with
bijective global-sections map. -/
@[stacks 0ELG] #check (SchemeOverField.genus X h_dimension hΓ : ℕ)

#check SchemeOverField.genus_def

#check
  (Curve.genus :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
      [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom], ℕ)

#check Curve.genus_def

end

section
variable (Y : Scheme.{u}) [IsLocallyNoetherian Y] [IsIntegral Y]

/- Exercise 111.61.1 (Definitions) (4): the Weil divisor class group of a locally Noetherian
integral scheme (in particular of a projective curve `X`) is `Div(Y) ⧸ Prin(Y)`. -/
@[stacks 0ELG] #check (WeilDivisorClassGroup Y : Type u)

#check (Cl(Y) : Type u)

#check (principalWeilDivisors Y)

#check (Prin(Y))

#check (weilDivisorClassGroupMk Y)

#check (weilDivisorClass_exactSequence Y)

end

section
variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [Curve X] [Projective X.hom]

/- Exercise 111.61.1 (Definitions) (5): a proper curve `X` is hyperelliptic when it admits a
linear series of degree `2` and dimension `1` (a `g¹₂`). -/
@[stacks 0ELG] #check (Curve.IsHyperelliptic X : Prop)

#check LinearSeries

#check (LinearSeries X (topologicalKrullDim_eq_one X).le 2 1)

#check (Curve.isHyperelliptic_iff X)

end

section

/- Exercise 111.61.1 (Definitions) (6): the intersection number of invertible modules with a
closed subscheme is the multilinear coefficient of its twist Euler-characteristic polynomial
(Stacks 0BEP). For curves `C`, `D` on a smooth projective surface `S` over `k`, the
intersection number `C · D` is this number for `𝒪(C)`, `𝒪(D)` on `S`, equivalently the
one-factor form `lineNumber` of `𝒪(C)` on `D`. -/
@[stacks 0ELG] #check
  (AlgebraicGeometry.Scheme.Modules.Intersection.number :
    ∀ (k : Type u) [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (Z : X.IdealSheafData) {d : ℕ},
      topologicalKrullDim Z.subscheme = d →
      ∀ [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
        (L : Fin d → X.Modules)
        [∀ j : Fin d, AlgebraicGeometry.Scheme.Modules.Invertible (L j)], ℚ)

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
