module

public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import ReasLib.Algebra.Homology.DifferentialGradedModule.MappingCone.Triangle

/-!
# The Triangulated Homotopy Category of Differential Graded Modules

The homotopy category of right modules over a cochain differential graded algebra carries its
intrinsic triangulated structure.  Distinguished triangles are the triangles isomorphic to the
explicit differential graded mapping-cone triangles.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule ZeroObject

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra R}

/-- The zero right differential graded module, with every graded component equal to the zero
`R`-module. -/
def zeroModule (A : CochainDGAlgebra R) : DifferentialGradedModule.{u, v} A where
  X := fun _ => 0
  d := fun _ => 0
  smul := fun _ _ => 0
  d_sq := sorry
  smul_one := sorry
  smul_mul := sorry
  comm_d := sorry

/-- The explicit zero differential graded module is a zero object. -/
theorem zeroModule_isZero (A : CochainDGAlgebra R) :
    IsZero (zeroModule.{u, v} A) := sorry

/-- Right differential graded modules have the canonical degreewise zero object. -/
noncomputable instance hasZeroObject (A : CochainDGAlgebra R) :
    HasZeroObject (DifferentialGradedModule.{u, v} A) where
  zero := ⟨zeroModule A, zeroModule_isZero A⟩

namespace Homotopy

/-- The intrinsic distinguished triangles in the differential graded homotopy category are
those isomorphic to an explicit mapping-cone triangle. -/
def distinguished (A : CochainDGAlgebra R) :
    Set (Triangle (K R (DifferentialGradedModule.{u, v} A))) :=
  { T | ∃ (X Y : DifferentialGradedModule.{u, v} A) (f : X ⟶ Y),
      Nonempty (T ≅ MappingCone.triangleK f) }

/-- Membership in the intrinsic distinguished family is exactly the existence of a
mapping-cone presentation. -/
theorem mem_distinguished (A : CochainDGAlgebra R)
    (T : Triangle (K R (DifferentialGradedModule.{u, v} A))) :
    T ∈ distinguished A ↔
      ∃ (X Y : DifferentialGradedModule.{u, v} A) (f : X ⟶ Y),
        Nonempty (T ≅ MappingCone.triangleK f) := sorry

/-- The differential graded homotopy category has the zero object represented by the zero
differential graded module. -/
noncomputable instance hasZeroObject (A : CochainDGAlgebra R) :
    HasZeroObject (K R (DifferentialGradedModule.{u, v} A)) :=
  (toK A).hasZeroObject_of_additive

/-- Lemma 22.10.1 (09KH): the homotopy category of right differential graded modules is
pretriangulated, with distinguished triangles represented by mapping cones. -/
@[stacks 09KH]
noncomputable instance pretriangulated (A : CochainDGAlgebra R) :
    Pretriangulated (K R (DifferentialGradedModule.{u, v} A)) where
  distinguishedTriangles := distinguished A
  isomorphic_distinguished := sorry
  contractible_distinguished := sorry
  distinguished_cocone_triangle := sorry
  rotate_distinguished_triangle := sorry
  complete_distinguished_triangle_morphism := sorry

/-- The abstract distinguished triangles are exactly the intrinsic mapping-cone triangles up to
isomorphism. -/
theorem distTriang_eq (A : CochainDGAlgebra R) :
    distTriang (K R (DifferentialGradedModule.{u, v} A)) = distinguished A := sorry

/-- Every explicit differential graded mapping-cone triangle is distinguished. -/
@[simp]
theorem mappingCone_triangleK_distinguished (A : CochainDGAlgebra R)
    {X Y : DifferentialGradedModule.{u, v} A} (f : X ⟶ Y) :
    MappingCone.triangleK f ∈
      distTriang (K R (DifferentialGradedModule.{u, v} A)) := sorry

/-- Proposition 22.10.3 (09KJ): the homotopy category of right differential graded modules
satisfies the octahedron axiom. -/
@[stacks 09KJ]
instance isTriangulated (A : CochainDGAlgebra R) :
    IsTriangulated (K R (DifferentialGradedModule.{u, v} A)) := sorry

end Homotopy

end DifferentialGradedModule
