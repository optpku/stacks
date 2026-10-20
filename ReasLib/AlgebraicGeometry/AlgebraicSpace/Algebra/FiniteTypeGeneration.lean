/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.RingTheory.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Finite-type quasi-coherent subalgebras

On a quasi-compact quasi-separated algebraic space, every quasi-coherent `𝒪_X`-algebra is
the directed colimit of its finite-type quasi-coherent subalgebras. Finite type is tested on
affine étale objects via `RingHom.FiniteType` of the structure-map components.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

/-- The structure morphism of an `𝒪_X`-algebra on an étale object, as a component of the
underlying natural transformation. -/
abbrev structureHom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (B : Under (commStructureSheaf X)) (U : smallEtaleSite X) :
    (commStructureSheaf X).obj.obj (op U) ⟶ B.right.obj.obj (op U) :=
  (InducedCategory.Hom.hom B.hom).app (op U)

/-- `structureHom B U` is the `U`-component of the algebra structure morphism. -/
theorem structureHom_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (B : Under (commStructureSheaf X)) (U : smallEtaleSite X) :
    structureHom B U = (InducedCategory.Hom.hom B.hom).app (op U) :=
  rfl

/-- An algebra over the structure sheaf is of finite type when each structure-map
component on an affine étale object is a finite-type ring homomorphism. -/
def finiteTypeProperty {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ObjectProperty (Under (commStructureSheaf X)) :=
  fun B ↦ ∀ (U : smallEtaleSite X), IsAffine U.left.left →
    RingHom.FiniteType (structureHom B U).hom

/-- Finite type of an `𝒪_X`-algebra is equivalent to finite type of the structure-map
components on affine étale objects. -/
theorem finiteTypeProperty_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (B : Under (commStructureSheaf X)) :
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
  {B | qcAlgebraUnderProperty X (B : Under (commStructureSheaf X)) ∧
      finiteTypeProperty X (B : Under (commStructureSheaf X))}

/-- A subalgebra belongs to `finiteTypeQuasiCoherentSubalgebras A` exactly when its carrier
algebra is quasi-coherent and of finite type. -/
@[simp] theorem mem_finiteTypeQuasiCoherentSubalgebras {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) (B : Subobject A.obj) :
    B ∈ finiteTypeQuasiCoherentSubalgebras A ↔
      qcAlgebraUnderProperty X (B : Under (commStructureSheaf X)) ∧
        finiteTypeProperty X (B : Under (commStructureSheaf X)) :=
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

/-- The inclusion diagram of the finite-type quasi-coherent subalgebras of an algebra,
indexed by their inherited inclusion order. -/
def finiteTypeSubalgebraDiagram {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) :
    finiteTypeQuasiCoherentSubalgebras A ⥤ Under (commStructureSheaf X) :=
  (show Monotone (fun B : finiteTypeQuasiCoherentSubalgebras A ↦ B.val) from
    fun _ _ h ↦ h).functor ⋙ Subobject.underlying

/-- The canonical inclusions of finite-type quasi-coherent subalgebras form a cocone
with point the ambient algebra. -/
def finiteTypeSubalgebraCocone {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) : CategoryTheory.Limits.Cocone (finiteTypeSubalgebraDiagram A) where
  pt := A.obj
  ι :=
    { app := fun B ↦ B.val.arrow
      naturality := fun B C f ↦ by
        change (finiteTypeSubalgebraDiagram A).map f ≫ C.val.arrow =
          B.val.arrow ≫ 𝟙 A.obj
        rw [Category.comp_id]
        exact Subobject.underlying_arrow
            ((show Monotone (fun B : finiteTypeQuasiCoherentSubalgebras A ↦ B.val) from
              fun _ _ h ↦ h).functor.map f) }

/-- Each leg of the canonical subalgebra cocone is the corresponding subobject inclusion. -/
@[simp] theorem finiteTypeSubalgebraCocone_ι_app {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) (B : finiteTypeQuasiCoherentSubalgebras A) :
    (finiteTypeSubalgebraCocone A).ι.app B = B.val.arrow :=
  rfl

/-- On a quasi-compact quasi-separated algebraic space, the finite-type quasi-coherent
subalgebras form a nonempty directed family whose inclusion cocone has the colimit
universal property in the category of algebras over the structure sheaf. -/
theorem finiteTypeQuasiCoherentSubalgebras_directedColimit
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (A : X.QcAlgebraUnder) :
    (finiteTypeQuasiCoherentSubalgebras A).Nonempty ∧
      DirectedOn (· ≤ ·) (finiteTypeQuasiCoherentSubalgebras A) ∧
        (∀ c : CategoryTheory.Limits.Cocone (finiteTypeSubalgebraDiagram A),
          ∃! f : A.obj ⟶ c.pt, ∀ B : finiteTypeQuasiCoherentSubalgebras A,
            B.val.arrow ≫ f = c.ι.app B) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder
