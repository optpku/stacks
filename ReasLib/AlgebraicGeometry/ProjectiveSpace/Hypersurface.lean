/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Coordinate
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.IdealClosure
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Topology.Irreducible

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme

section

variable {R : Type u} [CommRing R]

/-- A homogeneous polynomial defines a projective closed subscheme when its principal ideal
recovers the defining ideal on every standard coordinate chart. -/
def HasHomogeneousEquation
    (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData)
    (F : MvPolynomial (Fin (n + 1)) R) : Prop :=
  F.IsHomogeneous F.totalDegree ∧
    ∀ i : Fin (n + 1),
      Ideal.map (ProjectiveSpace.coordinateAwayToLocalization (R := R) n i)
          (Ideal.comap (ProjectiveSpace.coordinateBasicOpenIsoAway (R := R) n i).hom.hom
            (Z.ideal
              (ProjectiveSpace.coordinateBasicOpen (R := R) n i))) =
        Ideal.map
          (algebraMap (MvPolynomial (Fin (n + 1)) R)
            (ProjectiveSpace.coordinateLocalizationAway (R := R) n i))
          (Ideal.span {F})

/-- A closed subscheme lies on the hypersurface of a polynomial when the polynomial's principal
ideal is contained in the defining ideal on every standard coordinate chart. -/
def liesOnHypersurface (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData)
    (F : MvPolynomial (Fin (n + 1)) R) : Prop :=
  ∀ i : Fin (n + 1),
    Ideal.map (algebraMap (MvPolynomial (Fin (n + 1)) R)
        (ProjectiveSpace.coordinateLocalizationAway n i))
      (Ideal.span {F}) ≤
    Ideal.map (ProjectiveSpace.coordinateAwayToLocalization n i)
      (Ideal.comap (ProjectiveSpace.coordinateBasicOpenIsoAway n i).hom.hom
        (Z.ideal (ProjectiveSpace.coordinateBasicOpen n i)))

/-- The predicate that a closed subscheme lies on a hypersurface unfolds to chartwise ideal
containment. -/
theorem liesOnHypersurface_iff (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData)
    (F : MvPolynomial (Fin (n + 1)) R) :
    liesOnHypersurface n Z F ↔
      ∀ i : Fin (n + 1),
        Ideal.map (algebraMap (MvPolynomial (Fin (n + 1)) R)
            (ProjectiveSpace.coordinateLocalizationAway n i))
          (Ideal.span {F}) ≤
        Ideal.map (ProjectiveSpace.coordinateAwayToLocalization n i)
          (Ideal.comap (ProjectiveSpace.coordinateBasicOpenIsoAway n i).hom.hom
            (Z.ideal (ProjectiveSpace.coordinateBasicOpen n i))) := sorry

/-- Equality with the hypersurface defined by a homogeneous equation implies hypersurface
containment. -/
theorem liesOnHypersurface_of_hasHomogeneousEquation
    (n : ℕ) (Z : (ProjectiveSpace.scheme R n).IdealSheafData)
    (F : MvPolynomial (Fin (n + 1)) R) (h : HasHomogeneousEquation n Z F) :
    liesOnHypersurface n Z F := sorry

end

end AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme

namespace AlgebraicGeometry.ProjectiveSpace

section

variable {k : Type u} [Field k]

/-- The projective zero loci of two homogeneous irreducible polynomials of positive degree in
`k[X₀, X₁, X₂]` have nonempty intersection. -/
theorem zeroLocus_inter_nonempty
    (F₁ F₂ : MvPolynomial (Fin 3) k)
    (hF₁ : F₁.IsHomogeneous F₁.totalDegree) (hF₂ : F₂.IsHomogeneous F₂.totalDegree)
    (hdeg₁ : 0 < F₁.totalDegree) (hdeg₂ : 0 < F₂.totalDegree)
    (hirr₁ : Irreducible F₁) (hirr₂ : Irreducible F₂) :
    (ProjectiveSpectrum.zeroLocus (grading k 2) ({F₁} : Set (MvPolynomial (Fin 3) k)) ∩
      ProjectiveSpectrum.zeroLocus (grading k 2) ({F₂} : Set (MvPolynomial (Fin 3) k))).Nonempty :=
  sorry

end

namespace ClosedSubscheme

section

variable {R : Type u} [CommRing R]

/-- The support of a closed subscheme of projective `n`-space cut out by a homogeneous
equation `F` is the projective zero locus of `F`. -/
theorem support_eq_zeroLocus
    (n : ℕ) (Z : (scheme R n).IdealSheafData)
    (F : MvPolynomial (Fin (n + 1)) R)
    (hF : HasHomogeneousEquation n Z F) :
    (Z.support : Set (scheme R n)) =
      ProjectiveSpectrum.zeroLocus (grading R n)
        ({F} : Set (MvPolynomial (Fin (n + 1)) R)) :=
  sorry

end

section

variable {k : Type u} [Field k]

/-- Two irreducible projective plane hypersurfaces of positive degree have nonempty
intersection of their underlying closed supports. -/
theorem hypersurface_inter_nonempty
    (Z₁ Z₂ : (scheme k 2).IdealSheafData)
    (hZ₁ : IrreducibleSpace Z₁.subscheme) (hZ₂ : IrreducibleSpace Z₂.subscheme)
    (F₁ F₂ : MvPolynomial (Fin 3) k)
    (hF₁ : ClosedSubscheme.HasHomogeneousEquation 2 Z₁ F₁)
    (hF₂ : ClosedSubscheme.HasHomogeneousEquation 2 Z₂ F₂)
    (hdeg₁ : 0 < F₁.totalDegree) (hdeg₂ : 0 < F₂.totalDegree)
    (hirr₁ : Irreducible F₁) (hirr₂ : Irreducible F₂) :
    ((Z₁.support ⊓ Z₂.support : TopologicalSpace.Closeds (scheme k 2)) :
      Set (scheme k 2)).Nonempty :=
  sorry

end

end ClosedSubscheme

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.ProjectiveSpace.Hypersurface

open CategoryTheory

noncomputable section

variable {A : Type u} [CommRing A] (n d : ℕ)
variable (F : MvPolynomial (Fin (n + 1)) A) (hF : F ∈ ProjectiveSpace.grading A n d)

/-- The homogeneous principal ideal generated by a degree-`d` form in the homogeneous
coordinate ring of projective `n`-space. -/
def homogeneousIdeal : HomogeneousIdeal (ProjectiveSpace.grading A n) where
  toSubmodule := Ideal.span {F}
  is_homogeneous' :=
    GradedAlgebra.Quotient.spanSingleton_isHomogeneous (ProjectiveSpace.grading A n) ⟨d, hF⟩

/-- The underlying ideal of the homogeneous ideal generated by `F` is `Ideal.span {F}`. -/
theorem homogeneousIdeal_toIdeal :
    (homogeneousIdeal n d F hF).toIdeal = Ideal.span {F} := sorry

/-- The quotient grading on the homogeneous coordinate ring modulo the principal ideal
generated by `F`. -/
abbrev quotientGrading :
    ℕ → Submodule A (MvPolynomial (Fin (n + 1)) A ⧸ (homogeneousIdeal n d F hF).toIdeal) :=
  GradedAlgebra.Quotient.grading (ProjectiveSpace.grading A n)
    (homogeneousIdeal n d F hF).toIdeal

/-- The quotient by a homogeneous principal ideal carries its canonical graded-algebra
structure. -/
instance instGradedAlgebra : GradedAlgebra (quotientGrading n d F hF) :=
  GradedAlgebra.Quotient.gradedAlgebra (ProjectiveSpace.grading A n)
    (homogeneousIdeal n d F hF).toIdeal (homogeneousIdeal n d F hF).isHomogeneous

/-- The projective hypersurface defined by `F`, realized as the projective spectrum of the
homogeneous coordinate ring modulo `Ideal.span {F}`. -/
abbrev scheme : Scheme :=
  Proj (quotientGrading n d F hF)

/-- The quotient-induced morphism from the projective hypersurface defined by `F` to
projective `n`-space. -/
def closedImmersion : scheme n d F hF ⟶ ProjectiveSpace.scheme A n :=
  projQuotientMap (ProjectiveSpace.grading A n) (homogeneousIdeal n d F hF)

/-- The quotient-induced morphism of a projective hypersurface is a closed immersion. -/
instance instIsClosedImmersion : IsClosedImmersion (closedImmersion n d F hF) :=
  projQuotientMap_isClosedImmersion (ProjectiveSpace.grading A n) (homogeneousIdeal n d F hF)

/-- The structure morphism of the projective hypersurface defined by `F` to `Spec A`. -/
abbrev hom : scheme n d F hF ⟶ Spec (.of A) :=
  closedImmersion n d F hF ≫ ProjectiveSpace.toSpec A n

end

end AlgebraicGeometry.ProjectiveSpace.Hypersurface
