/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.MappingCone.Functoriality

/-!
# Isomorphisms of differential graded mapping cones

Vertical isomorphisms of a commutative square induce isomorphisms of mapping cones.  The
construction is kept separate from the coordinate and triangle layers so clients that only need
invariance under isomorphism do not import additional triangle infrastructure.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule.MappingCone

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [HasBinaryBiproducts (ringedSiteModuleCategory J 𝒪)]
variable {𝒜 : DGA(𝒪)}
variable {K L K' L' : Mod(𝒜, d)}
variable {f : K ⟶ L} {g : K' ⟶ L'}
variable {a : K ⟶ K'} {b : L ⟶ L'}

/-- Reversing both vertical isomorphisms gives the inverse commutative square. -/
theorem inverseSquare (sq : CommSq f a b g) [IsIso a] [IsIso b] :
    CommSq g (inv a) (inv b) f :=
  CommSq.vert_inv (g := asIso a) (h := asIso b) sq

/-- The canonical mapping-cone isomorphism, with the block-diagonal map of the inverse
square as its specified inverse. -/
noncomputable def iso (sq : CommSq f a b g) [IsIso a] [IsIso b] :
    mappingCone f ≅ mappingCone g where
  hom := map sq
  inv := map (inverseSquare sq)
  hom_inv_id := by
    simpa only [IsIso.hom_inv_id, map_id] using
      (map_comp sq (inverseSquare sq)).symm
  inv_hom_id := by
    simpa only [IsIso.inv_hom_id, map_id] using
      (map_comp (inverseSquare sq) sq).symm

/-- A commutative square with isomorphic vertical sides induces an isomorphism of mapping cones. -/
instance map_isIso (sq : CommSq f a b g) [IsIso a] [IsIso b] : IsIso (map sq) :=
  (iso sq).isIso_hom

/-- The hom of the canonical mapping-cone isomorphism is the block-diagonal cone map. -/
@[simp]
theorem iso_hom (sq : CommSq f a b g) [IsIso a] [IsIso b] :
    (iso sq).hom = map sq := rfl

/-- The inverse is the block-diagonal map of the inverse square. -/
@[simp]
theorem iso_inv_map (sq : CommSq f a b g) [IsIso a] [IsIso b] :
    (iso sq).inv = map (inverseSquare sq) := rfl

/-- The inverse of the canonical mapping-cone isomorphism is the categorical inverse of its
block-diagonal cone map. -/
@[simp]
theorem iso_inv (sq : CommSq f a b g) [IsIso a] [IsIso b] :
    (iso sq).inv = inv (map sq) := by
  exact (IsIso.inv_eq_of_hom_inv_id (iso sq).hom_inv_id).symm

/-- The canonical isomorphism of module-level mapping-cone triangles, with inverse given
by the triangle map of the inverse square. -/
noncomputable def triangleIso (sq : CommSq f a b g) [IsIso a] [IsIso b] :
    triangle f ≅ triangle g where
  hom := triangleMap sq
  inv := triangleMap (inverseSquare sq)
  hom_inv_id := by
    simpa only [IsIso.hom_inv_id, triangleMap_id] using
      (triangleMap_comp sq (inverseSquare sq)).symm
  inv_hom_id := by
    simpa only [IsIso.inv_hom_id, triangleMap_id] using
      (triangleMap_comp (inverseSquare sq) sq).symm

/-- A square of vertical isomorphisms induces an isomorphism of the associated mapping-cone
triangles. -/
instance triangleMap_isIso (sq : CommSq f a b g) [IsIso a] [IsIso b] :
    IsIso (triangleMap sq) :=
  (triangleIso sq).isIso_hom

/-- The hom of the canonical triangle isomorphism is the induced triangle map. -/
@[simp]
theorem triangleIso_hom (sq : CommSq f a b g) [IsIso a] [IsIso b] :
    (triangleIso sq).hom = triangleMap sq := rfl

/-- The inverse of the triangle isomorphism is the triangle map of the inverse square. -/
@[simp]
theorem triangleIso_inv (sq : CommSq f a b g) [IsIso a] [IsIso b] :
    (triangleIso sq).inv = triangleMap (inverseSquare sq) := rfl

/-- The canonical homotopy-category isomorphism is the image of the explicit module-level
triangle isomorphism. -/
noncomputable def triangleIsoK (sq : CommSq f a b g) [IsIso a] [IsIso b] :
    triangleK f ≅ triangleK g :=
  (toK 𝒜).mapTriangle.mapIso (triangleIso sq)

/-- The homotopy-category image of a square of vertical isomorphisms induces an isomorphism of
mapping-cone triangles. -/
instance triangleMapK_isIso (sq : CommSq f a b g) [IsIso a] [IsIso b] :
    IsIso (triangleMapK sq) :=
  (triangleIsoK sq).isIso_hom

end

end SheafOfModules.RingedSite.DifferentialGradedModule.MappingCone
