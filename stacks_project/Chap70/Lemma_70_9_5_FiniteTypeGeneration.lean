module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.FiniteTypeGeneration
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

#check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.structureHom :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (B : Under (commRingStructureSheaf X)) (U : smallEtaleSite X),
    (commRingStructureSheaf X).obj.obj (op U) ⟶ B.right.obj.obj (op U))

#check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.structureHom_eq :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (B : Under (commRingStructureSheaf X)) (U : smallEtaleSite X),
    structureHom B U = (InducedCategory.Hom.hom B.hom).app (op U))

#check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.finiteTypeProperty :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    ObjectProperty (Under (commRingStructureSheaf X)))

#check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.finiteTypeProperty_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (B : Under (commRingStructureSheaf X)),
    finiteTypeProperty X B ↔
      ∀ (U : smallEtaleSite X), IsAffine U.left.left →
        RingHom.FiniteType (structureHom B U).hom)

#check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.finiteTypeProperty_iff_sectionRing :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder),
    finiteTypeProperty X A.obj ↔
      ∀ (U : smallEtaleSite X), IsAffine U.left.left →
        Algebra.FiniteType Γ(U.left.left, ⊤) (sectionRing A U))

#check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.finiteTypeQuasiCoherentSubalgebras :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder), Set (Subobject A.obj))

#check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.mem_finiteTypeQuasiCoherentSubalgebras :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) (B : Subobject A.obj),
    B ∈ finiteTypeQuasiCoherentSubalgebras A ↔
      qcAlgebraUnderProperty X (B : Under (commRingStructureSheaf X)) ∧
        finiteTypeProperty X (B : Under (commRingStructureSheaf X)))

#check
  (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.finiteTypeQuasiCoherentSubalgebras_isDirectedColimit :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
      [IsAbsolutelyQuasiSeparated X] (A : X.QcAlgebraUnder),
      DirectedOn (· ≤ ·) (finiteTypeQuasiCoherentSubalgebras A) ∧
        IsLUB (finiteTypeQuasiCoherentSubalgebras A) (⊤ : Subobject A.obj))

end AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder
