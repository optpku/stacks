module

public import Mathlib.RingTheory.FiniteType
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Presentation

/-!
# Finite type of graded algebra sheaves and relative projective spectra

Finite type over the degree-zero algebra and over the base are equivalent when the
degree-zero module is finite and the commutative graded algebra is quasicoherent.
The structure morphism of an étale-local relative projective spectrum is of finite type
when its quasicoherent commutative graded algebra is of finite type over the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A graded `𝒪_X`-algebra is of finite type as an `𝒜_0`-algebra when every affine étale chart
admits a one-and-mul-preserving `Type u` model whose ambient ring is of finite type over degree
zero. -/
def FiniteTypeAsDegreeZeroAlgebra
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)) : Prop :=
  ∀ U : affineEtaleSite X,
    ∃ (A : Type u) (hA : CommRing A) (grading : ℕ → Submodule ℤ A)
      (hgraded : GradedAlgebra grading)
      (model : ∀ d : ℕ,
        (𝒜.obj (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d)),
      IsEtaleSectionModel 𝒜 U.obj grading model ∧
        RingHom.FiniteType (algebraMap (grading 0) A)

/-- Finite type as an `𝒜_0`-algebra is the affine-étale existence of a one-and-mul-preserving
`Type u` model of finite type over degree zero. -/
theorem finiteTypeAsDegreeZeroAlgebra_iff
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)) :
    FiniteTypeAsDegreeZeroAlgebra 𝒜 ↔
      ∀ U : affineEtaleSite X,
        ∃ (A : Type u) (hA : CommRing A) (grading : ℕ → Submodule ℤ A)
          (hgraded : GradedAlgebra grading)
          (model : ∀ d : ℕ,
            (𝒜.obj (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d)),
          IsEtaleSectionModel 𝒜 U.obj grading model ∧
            RingHom.FiniteType (algebraMap (grading 0) A) :=
  Iff.rfl

/-- A graded `𝒪_X`-algebra is of finite type as an `𝒪_X`-algebra when every affine étale chart
admits a one-and-mul-preserving `Type u` model whose canonical structure map is of finite type. -/
def FiniteTypeAsBaseAlgebra
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)) : Prop :=
  ∀ U : affineEtaleSite X,
    ∃ (A : Type u) (hA : CommRing A) (grading : ℕ → Submodule ℤ A)
      (hgraded : GradedAlgebra grading)
      (model : ∀ d : ℕ,
        (𝒜.obj (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
      (hModel : IsEtaleSectionModel 𝒜 U.obj grading model),
      RingHom.FiniteType (etaleBaseToRing U model hModel)

/-- Finite type as an `𝒪_X`-algebra is the affine-étale existence of a one-and-mul-preserving
`Type u` model whose canonical structure map is of finite type. -/
theorem finiteTypeAsBaseAlgebra_iff
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)) :
    FiniteTypeAsBaseAlgebra 𝒜 ↔
      ∀ U : affineEtaleSite X,
        ∃ (A : Type u) (hA : CommRing A) (grading : ℕ → Submodule ℤ A)
          (hgraded : GradedAlgebra grading)
          (model : ∀ d : ℕ,
            (𝒜.obj (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
          (hModel : IsEtaleSectionModel 𝒜 U.obj grading model),
          RingHom.FiniteType (etaleBaseToRing U model hModel) :=
  Iff.rfl

/-- For a quasicoherent commutative graded algebra sheaf with finite degree-zero module,
finite type over degree zero is equivalent to finite type over the base. -/
theorem finiteTypeConditions_iff
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    (deg : DegreePieces 𝒜) :
    ((deg.obj 0).IsFiniteType ∧ FiniteTypeAsDegreeZeroAlgebra 𝒜) ↔
      ((deg.obj 0).IsFiniteType ∧ FiniteTypeAsBaseAlgebra 𝒜) := sorry

/-- A morphism that is étale-locally the scheme projective spectrum of a quasicoherent
commutative graded algebra sheaf, via its canonical chart structure morphisms, is of finite
type when the algebra sheaf is of finite type over the base. -/
theorem finiteType_of_finiteTypeAsBase
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X))
    [𝒜.IsCommutative] (hqc : 𝒜.IsQuasicoherent)
    {P : AlgebraicSpace S} (π : P ⟶ X)
    (hπ : IsEtaleLocallyProj 𝒜 π)
    (h𝒜 : FiniteTypeAsBaseAlgebra 𝒜) : AlgebraicSpace.FiniteType π := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
