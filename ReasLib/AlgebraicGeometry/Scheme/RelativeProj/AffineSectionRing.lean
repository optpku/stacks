/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GradedAlgebraSections
public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# The actual graded section algebra for an affine relative-Proj model

The ring is the direct sum of the nonnegative global sections. Scalar action
and grading are built from those same components. The degree-zero piece is
not assumed to equal the base ring.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry Opposite
open SheafOfModules.RingedSite
open scoped DirectSum
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.RelativeProjAffineSectionRing

variable {S : Scheme.{u}} (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) [𝒜.IsCommutative]

/-- The actual base ring of global functions. -/
abbrev baseRing (S : Scheme.{u}) : CommRingCat.{u} := S.presheaf.obj (op ⊤)

/-- The actual direct sum of homogeneous global sections. -/
abbrev ring : Type u := RingedSpace.GradedAlgebraSections.ring 𝒜

/-- The scalar map sends r to r times the given degree-zero unit. -/
instance homogeneousAlgebra :
    DirectSum.GAlgebra (baseRing S) (RingedSpace.GradedAlgebraSections.degree 𝒜) where
  toFun :=
    { toFun := fun r ↦ r • 𝒜.one (op ⊤)
      map_zero' := zero_smul _ _
      map_add' := fun r s ↦ add_smul r s _ }
  map_one := one_smul _ _
  map_mul := sorry
  commutes := sorry
  smul_def := sorry

/-- The same homogeneous summands, as submodules over the actual base ring. -/
def grading (n : ℕ) : Submodule (baseRing S) (ring 𝒜) where
  carrier := RingedSpace.GradedAlgebraSections.grading 𝒜 n
  zero_mem' := (RingedSpace.GradedAlgebraSections.grading 𝒜 n).zero_mem
  add_mem' := (RingedSpace.GradedAlgebraSections.grading 𝒜 n).add_mem
  smul_mem' := sorry

/-- The canonical homogeneous inclusion and projection, as a linear equivalence. -/
def gradeEquiv (n : ℕ) :
    RingedSpace.GradedAlgebraSections.degree 𝒜 n ≃ₗ[baseRing S] grading 𝒜 n where
  toFun x :=
    ⟨(RingedSpace.GradedAlgebraSections.gradeEquiv 𝒜 n x).1,
      (RingedSpace.GradedAlgebraSections.gradeEquiv 𝒜 n x).2⟩
  invFun x := (RingedSpace.GradedAlgebraSections.gradeEquiv 𝒜 n).symm ⟨x.1, x.2⟩
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry
  map_smul' := sorry

/-- The internal grading uses the actual direct-sum coordinate decomposition. -/
instance grading_decomposition : DirectSum.Decomposition (grading 𝒜) where
  decompose' := (DirectSum.congrAddEquiv (fun n ↦ (gradeEquiv 𝒜 n).toAddEquiv)).toAddMonoidHom
  left_inv := sorry
  right_inv := sorry

/-- Unit and products land in their prescribed homogeneous summands. -/
instance grading_monoid : SetLike.GradedMonoid (grading 𝒜) where
  toGradedOne := { one_mem := sorry }
  toGradedMul := { mul_mem := sorry }

instance grading_algebra : GradedAlgebra (grading 𝒜) :=
  { (inferInstance : DirectSum.Decomposition (grading 𝒜)),
    (inferInstance : SetLike.GradedMonoid (grading 𝒜)) with }

/-- The actual base-ring map into degree zero; it need not be an isomorphism. -/
def baseToZero : baseRing S →+* grading 𝒜 0 where
  toFun r := ⟨algebraMap (baseRing S) (ring 𝒜) r, sorry⟩
  map_one' := Subtype.ext (map_one (algebraMap (baseRing S) (ring 𝒜)))
  map_mul' r s := Subtype.ext (map_mul (algebraMap (baseRing S) (ring 𝒜)) r s)
  map_zero' := Subtype.ext (map_zero (algebraMap (baseRing S) (ring 𝒜)))
  map_add' r s := Subtype.ext (map_add (algebraMap (baseRing S) (ring 𝒜)) r s)

/-- The projective spectrum of this actual section ring. -/
def scheme : Scheme.{u} := Proj (grading 𝒜)

/-- Its structure map over the affine base, using the actual affine Spec comparison. -/
def toBase [IsAffine S] : scheme 𝒜 ⟶ S :=
  Proj.toSpecZero (grading 𝒜) ≫ Spec.map (CommRingCat.ofHom (baseToZero 𝒜)) ≫ S.isoSpec.inv

end AlgebraicGeometry.Scheme.RelativeProjAffineSectionRing
