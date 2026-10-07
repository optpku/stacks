module

public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.RingTheory.FiniteType
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Lemma_67_48_1_QcAlgebra

/-!
# Finite-type quasi-coherent subalgebras

On a quasi-compact quasi-separated algebraic space, every quasi-coherent `𝒪_X`-algebra is
the directed colimit of its finite-type quasi-coherent subalgebras. Finite type is tested on
affine étale objects via `RingHom.FiniteType` of the structure-map components.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

/-- The structure morphism of an `𝒪_X`-algebra on an étale object, as a component of the
underlying natural transformation. -/
abbrev structureHom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (B : Under (commRingStructureSheaf X)) (U : smallEtaleSite X) :
    (commRingStructureSheaf X).obj.obj (op U) ⟶ B.right.obj.obj (op U) :=
  (InducedCategory.Hom.hom B.hom).app (op U)

/-- `structureHom B U` is the `U`-component of the algebra structure morphism. -/
theorem structureHom_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (B : Under (commRingStructureSheaf X)) (U : smallEtaleSite X) :
    structureHom B U = (InducedCategory.Hom.hom B.hom).app (op U) :=
  rfl

/-- An `𝒪_X`-algebra is of finite type if its restriction to every affine scheme étale over `X`
is the tilde of a finite-type algebra over the affine coordinate ring. -/
def finiteTypeProperty {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ObjectProperty (Under (commRingStructureSheaf X)) :=
  fun B ↦ ∀ (U : smallEtaleSite X), IsAffine U.left.left →
    RingHom.FiniteType (structureHom B U).hom

/-- Finite type of an `𝒪_X`-algebra is equivalent to finite type of the structure-map
components on affine étale objects. -/
theorem finiteTypeProperty_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (B : Under (commRingStructureSheaf X)) :
    finiteTypeProperty X B ↔
      ∀ (U : smallEtaleSite X), IsAffine U.left.left →
        RingHom.FiniteType (structureHom B U).hom :=
  Iff.rfl

/-- For a quasi-coherent `𝒪_X`-algebra, finite type is equivalent to `Algebra.FiniteType` of
the section rings over affine étale objects. -/
theorem finiteTypeProperty_iff_sectionRing {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) :
    finiteTypeProperty X A.obj ↔
      ∀ (U : smallEtaleSite X), IsAffine U.left.left →
        Algebra.FiniteType Γ(U.left.left, ⊤) (sectionRing A U) :=
  sorry

/-- The finite-type quasi-coherent subalgebras of a quasi-coherent `𝒪_X`-algebra. -/
def finiteTypeQuasiCoherentSubalgebras {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) : Set (Subobject A.obj) :=
  {B | qcAlgebraUnderProperty X (B : Under (commRingStructureSheaf X)) ∧
      finiteTypeProperty X (B : Under (commRingStructureSheaf X))}

/-- A subalgebra belongs to `finiteTypeQuasiCoherentSubalgebras A` exactly when its carrier
algebra is quasi-coherent and of finite type. -/
@[simp] theorem mem_finiteTypeQuasiCoherentSubalgebras {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) (B : Subobject A.obj) :
    B ∈ finiteTypeQuasiCoherentSubalgebras A ↔
      qcAlgebraUnderProperty X (B : Under (commRingStructureSheaf X)) ∧
        finiteTypeProperty X (B : Under (commRingStructureSheaf X)) :=
  Iff.rfl

/-- On a quasi-compact quasi-separated algebraic space, the finite-type quasi-coherent
subalgebras of a quasi-coherent `𝒪_X`-algebra are directed by inclusion and have supremum
the whole algebra. -/
theorem finiteTypeQuasiCoherentSubalgebras_isDirectedColimit
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (A : X.QcAlgebraUnder) :
    DirectedOn (· ≤ ·) (finiteTypeQuasiCoherentSubalgebras A) ∧
      IsLUB (finiteTypeQuasiCoherentSubalgebras A) (⊤ : Subobject A.obj) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder
