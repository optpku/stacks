module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Data.Fin.Rev
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Basic

@[expose] public section

open CategoryTheory
open scoped BigOperators

noncomputable section

universe u v w x

namespace AlgebraicGeometry.ChernClass

/-- The data relevant to the projective-bundle construction of the Chern classes of a
constant-rank finite locally free module.  The equivalence is the projective-bundle formula,
written using cup product in the cohomology ring and pullback along `p`. -/
structure ProjectiveBundleContext
    {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w})
    (A : Cᵒᵖ ⥤ RingCat.{x}) (X P : C) (E : (toScheme.obj X).Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (p : P ⟶ X)
    (hP : Scheme.ProjectiveBundle.Representation (toScheme.map p) E) where
  /-- The first Chern class of an invertible module. -/
  firstChernClass :
    ∀ (Y : C) (L : (toScheme.obj Y).Modules),
      Scheme.Modules.Invertible L → A.obj (Opposite.op Y)
  /-- The projective-bundle formula as an equivalence with the first `r` coefficients. -/
  projectiveBundleEquiv :
    (Fin r → A.obj (Opposite.op X)) ≃ A.obj (Opposite.op P)
  /-- The projective-bundle equivalence is given by powers of
  `c₁(𝒪_P(1))` cup pullbacks of its coefficients. -/
  projectiveBundleEquiv_apply : ∀ a,
    projectiveBundleEquiv a =
      ∑ i : Fin r,
        firstChernClass P
              (Scheme.ProjectiveBundle.tautologicalSheaf (toScheme.map p) hP)
              (Scheme.ProjectiveBundle.tautologicalSheaf_isInvertible (toScheme.map p) hP) ^
            i.1 *
          A.map p.op (a i)

namespace ProjectiveBundleContext

variable {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w})
  (A : Cᵒᵖ ⥤ RingCat.{x}) (X P : C) (E : (toScheme.obj X).Modules) (r : ℕ)
  [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (p : P ⟶ X)
  (hP : Scheme.ProjectiveBundle.Representation (toScheme.map p) E)

/-- Build the projective-bundle Chern context from a first Chern class and a verified
projective-bundle-formula equivalence. -/
def ofProjectiveBundleFormula
    (firstChernClass :
      ∀ (Y : C) (L : (toScheme.obj Y).Modules),
        Scheme.Modules.Invertible L → A.obj (Opposite.op Y))
    (projectiveBundleEquiv :
      (Fin r → A.obj (Opposite.op X)) ≃ A.obj (Opposite.op P))
    (projectiveBundleEquiv_apply : ∀ a,
      projectiveBundleEquiv a =
        ∑ i : Fin r,
          firstChernClass P
                (Scheme.ProjectiveBundle.tautologicalSheaf (toScheme.map p) hP)
                (Scheme.ProjectiveBundle.tautologicalSheaf_isInvertible (toScheme.map p) hP) ^
              i.1 *
            A.map p.op (a i)) :
    ProjectiveBundleContext toScheme A X P E r p hP where
  firstChernClass := firstChernClass
  projectiveBundleEquiv := projectiveBundleEquiv
  projectiveBundleEquiv_apply := projectiveBundleEquiv_apply

variable (S : ProjectiveBundleContext toScheme A X P E r p hP)

/-- The class `c₁(𝒪_P(1))` of the tautological invertible module on the projective
bundle. -/
def tautologicalFirstChernClass : A.obj (Opposite.op P) :=
  S.firstChernClass P
    (Scheme.ProjectiveBundle.tautologicalSheaf (toScheme.map p) hP)
    (Scheme.ProjectiveBundle.tautologicalSheaf_isInvertible (toScheme.map p) hP)

/-- The tautological first Chern class is obtained by applying the context's first Chern
class operation to `𝒪_P(1)`. -/
theorem tautologicalFirstChernClass_def :
    S.tautologicalFirstChernClass =
      S.firstChernClass P
        (Scheme.ProjectiveBundle.tautologicalSheaf (toScheme.map p) hP)
        (Scheme.ProjectiveBundle.tautologicalSheaf_isInvertible (toScheme.map p) hP) := sorry

/-- The signed projective-bundle coordinates of the negative top power of
`c₁(𝒪_P(1))`. -/
def signedChernCoordinates : Fin r → A.obj (Opposite.op X) :=
  S.projectiveBundleEquiv.symm
    (-((-1 : A.obj (Opposite.op P)) ^ r * S.tautologicalFirstChernClass ^ r))

/-- Applying the projective-bundle equivalence to the signed Chern coordinates gives the
negative top power of `c₁(𝒪_P(1))`. -/
theorem projectiveBundleEquiv_signedChernCoordinates :
    S.projectiveBundleEquiv S.signedChernCoordinates =
      -((-1 : A.obj (Opposite.op P)) ^ r * S.tautologicalFirstChernClass ^ r) := sorry

/-- The Chern classes `c^A_j(E)` determined by the projective-bundle formula, with
`c^A_0(E) = 1`. -/
def chernClass : Fin (r + 1) → A.obj (Opposite.op X) :=
  Fin.cons 1 fun (j : Fin r) ↦
    (-1 : A.obj (Opposite.op X)) ^ (Fin.rev j).1 *
      signedChernCoordinates toScheme A X P E r p hP S (Fin.rev j)

/-- The degree-zero Chern class determined by the projective-bundle formula is `1`. -/
theorem chernClass_zero :
    chernClass toScheme A X P E r p hP S 0 = 1 := sorry

/-- The alternating projective-bundle relation for the Chern classes determined by the context. -/
theorem chernClass_relation :
    ∑ i : Fin (r + 1),
      (-1 : A.obj (Opposite.op P)) ^ i.1 *
        S.tautologicalFirstChernClass ^ i.1 *
          A.map p.op
            (chernClass toScheme A X P E r p hP S (Fin.rev i)) = 0 := sorry

end ProjectiveBundleContext

end AlgebraicGeometry.ChernClass
