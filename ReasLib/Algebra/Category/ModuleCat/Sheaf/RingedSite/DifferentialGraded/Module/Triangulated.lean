/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.MappingCone.Triangle

/-!
# Triangulated DG homotopy category of module sheaves

The distinguished triangles are defined intrinsically in the DG homotopy category: they are
the triangles isomorphic to a canonical differential graded module mapping-cone triangle.  This
does not enlarge the class by forgetting module-linear homotopies.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule.Homotopy

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [HasBinaryBiproducts (ringedSiteModuleCategory J 𝒪)]

/-- The intrinsic distinguished triangles in the DG homotopy category of module sheaves. -/
@[stacks 0FS7]
def distinguished (𝒜 : DGA(𝒪)) :
    Set (Triangle (K ℤ Mod(𝒜, d))) :=
  { T | ∃ (X Y : Mod(𝒜, d)) (f : X ⟶ Y),
      Nonempty (T ≅ MappingCone.triangleK f) }

/-- A triangle is intrinsically distinguished exactly when it is isomorphic to a canonical
DG-module mapping-cone triangle. -/
theorem mem_distinguished (𝒜 : DGA(𝒪)) (T : Triangle (K ℤ Mod(𝒜, d))) :
    T ∈ distinguished 𝒜 ↔
      ∃ (X Y : Mod(𝒜, d)) (f : X ⟶ Y),
        Nonempty (T ≅ MappingCone.triangleK f) := sorry

/-- The DG homotopy category has the zero object represented by the zero differential graded
module. -/
noncomputable instance hasZeroObject (𝒜 : DGA(𝒪)) :
    HasZeroObject (K ℤ Mod(𝒜, d)) :=
  (toK 𝒜).hasZeroObject_of_additive

/-- The DG homotopy category of differential graded module sheaves is pretriangulated, with its
concrete distinguished-triangle data owned by `distinguished`. -/
noncomputable instance pretriangulated (𝒜 : DGA(𝒪)) :
    Pretriangulated (K ℤ Mod(𝒜, d)) where
  distinguishedTriangles := distinguished 𝒜
  isomorphic_distinguished := sorry
  contractible_distinguished := sorry
  distinguished_cocone_triangle := sorry
  rotate_distinguished_triangle := sorry
  complete_distinguished_triangle_morphism := sorry

/-- The abstract distinguished triangles are exactly the intrinsic mapping-cone triangles up to
isomorphism. -/
theorem distTriang_eq (𝒜 : DGA(𝒪)) :
    distTriang (K ℤ Mod(𝒜, d)) = distinguished 𝒜 := sorry

/-- The canonical mapping-cone triangle of every differential graded module morphism is
distinguished. -/
@[simp]
theorem mappingCone_triangleK_distinguished
    (𝒜 : DGA(𝒪)) {X Y : Mod(𝒜, d)} (f : X ⟶ Y) :
    MappingCone.triangleK f ∈ distTriang (K ℤ Mod(𝒜, d)) := sorry

/-- The DG homotopy category of differential graded module sheaves satisfies the octahedron
axiom. -/
@[stacks 0FS7]
instance isTriangulated (𝒜 : DGA(𝒪)) :
    IsTriangulated (K ℤ Mod(𝒜, d)) := sorry

end

end SheafOfModules.RingedSite.DifferentialGradedModule.Homotopy
