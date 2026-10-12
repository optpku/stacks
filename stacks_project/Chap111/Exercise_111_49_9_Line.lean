/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.Data.Fin.VecNotation
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist.Invertible
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback

/-!
# Lines in standard projective 3-space

This module owns the closed-immersion predicate for a line in `ℙ³_k`, together with the
standard linear embedding `ℙ¹_k ⟶ ℙ³_k` given by `(X 0 : X 1) ↦ (X 0 : X 0 : 0 : X 1)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- A closed immersion `i : Z ⟶ ℙ³_k` is a line when `Z` is isomorphic to `ℙ¹_k` and the
pullback of `𝒪(1)` has Picard class `𝒪(1)`. -/
class IsLine {k : Type u} [Field k] {Z : Scheme.{u}} (i : Z ⟶ scheme k 3) : Prop
    extends IsClosedImmersion i where
  /-- There is an isomorphism `ℙ¹_k ≅ Z` under which `𝒪(1)` pulls back to `𝒪(1)`. -/
  exists_iso_degree_one :
    ∃ e : scheme k 1 ≅ Z,
      Scheme.Hom.picardPullback (e.hom ≫ i)
          (Scheme.Modules.picardClass (twistingSheaf k 3 1)) =
        Scheme.Modules.picardClass (twistingSheaf k 1 1)

/-- A morphism to `ℙ³_k` is a line iff it is a closed immersion isomorphic to `ℙ¹_k` of
`𝒪(1)`-degree one. -/
theorem isLine_iff {k : Type u} [Field k] {Z : Scheme.{u}} (i : Z ⟶ scheme k 3) :
    IsLine i ↔
      IsClosedImmersion i ∧
        ∃ e : scheme k 1 ≅ Z,
          Scheme.Hom.picardPullback (e.hom ≫ i)
              (Scheme.Modules.picardClass (twistingSheaf k 3 1)) =
            Scheme.Modules.picardClass (twistingSheaf k 1 1) := sorry

/-- The linear substitution sending the four homogeneous coordinates of `ℙ³_k` to
`(X 0, X 0, 0, X 1)` in the homogeneous coordinate ring of `ℙ¹_k`. -/
def standardLineCoordinateImage (k : Type u) [Field k] :
    Fin (3 + 1) → MvPolynomial (Fin (1 + 1)) k :=
  ![MvPolynomial.X 0, MvPolynomial.X 0, 0, MvPolynomial.X 1]

/-- The standard line substitution is the displayed 4-tuple of homogeneous coordinates. -/
theorem standardLineCoordinateImage_eq (k : Type u) [Field k] :
    standardLineCoordinateImage k =
      ![MvPolynomial.X 0, MvPolynomial.X 0, 0, MvPolynomial.X 1] := sorry

/-- The ungraded ring homomorphism `k[T 0, T 1, T 2, T 3] →+* k[X 0, X 1]` extending
`standardLineCoordinateImage`. -/
def standardLineRingHom (k : Type u) [Field k] :
    MvPolynomial (Fin (3 + 1)) k →+* MvPolynomial (Fin (1 + 1)) k :=
  MvPolynomial.eval₂Hom (algebraMap k (MvPolynomial (Fin (1 + 1)) k))
    (standardLineCoordinateImage k)

/-- `standardLineRingHom` evaluates variables according to `standardLineCoordinateImage`. -/
theorem standardLineRingHom_X (k : Type u) [Field k] (i : Fin (3 + 1)) :
    standardLineRingHom k (MvPolynomial.X i) = standardLineCoordinateImage k i := sorry

/-- `standardLineRingHom` preserves the standard homogeneous grading. -/
theorem standardLineRingHom_map_mem {k : Type u} [Field k] {d : ℕ}
    {x : MvPolynomial (Fin (3 + 1)) k} (hx : x ∈ grading k 3 d) :
    standardLineRingHom k x ∈ grading k 1 d := sorry

/-- The graded ring homomorphism inducing the standard line `ℙ¹_k ⟶ ℙ³_k`. -/
def standardLineGradedHom (k : Type u) [Field k] : grading k 3 →+*ᵍ grading k 1 where
  toRingHom := standardLineRingHom k
  map_mem := standardLineRingHom_map_mem

/-- The graded substitution sends the irrelevant ideal of the line coordinate ring into the
image of the ambient irrelevant ideal. -/
theorem standardLineGradedHom_irrelevant (k : Type u) [Field k] :
    HomogeneousIdeal.irrelevant (grading k 1) ≤
      (HomogeneousIdeal.irrelevant (grading k 3)).map (standardLineGradedHom k) := sorry

/-- The scheme morphism `ℙ¹_k ⟶ ℙ³_k` induced by the standard linear coordinate substitution. -/
def standardLineHom (k : Type u) [Field k] : scheme k 1 ⟶ scheme k 3 :=
  Proj.map (standardLineGradedHom k) (standardLineGradedHom_irrelevant k)

/-- `standardLineHom` is a morphism of schemes over `Spec k`. -/
theorem standardLineHom_comp_toSpec (k : Type u) [Field k] :
    standardLineHom k ≫ toSpec k 3 = toSpec k 1 := sorry

/-- The standard linear embedding `ℙ¹_k ⟶ ℙ³_k` is a line. -/
instance instIsLine_standardLineHom (k : Type u) [Field k] :
    IsLine (standardLineHom k) := sorry

end AlgebraicGeometry.ProjectiveSpace
