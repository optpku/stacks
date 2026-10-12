/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

/-- A commutative square with isomorphic vertical sides induces an isomorphism of mapping cones. -/
instance map_isIso (sq : CommSq f a b g) [IsIso a] [IsIso b] : IsIso (map sq) := sorry

/-- The canonical mapping-cone isomorphism attached to a commutative square of vertical
isomorphisms. -/
noncomputable def iso (sq : CommSq f a b g) [IsIso a] [IsIso b] :
    mappingCone f ≅ mappingCone g :=
  asIso (map sq)

/-- The hom of the canonical mapping-cone isomorphism is the block-diagonal cone map. -/
@[simp]
theorem iso_hom (sq : CommSq f a b g) [IsIso a] [IsIso b] :
    (iso sq).hom = map sq := sorry

/-- The inverse of the canonical mapping-cone isomorphism is the categorical inverse of its
block-diagonal cone map. -/
@[simp]
theorem iso_inv (sq : CommSq f a b g) [IsIso a] [IsIso b] :
    (iso sq).inv = inv (map sq) := sorry

/-- A square of vertical isomorphisms induces an isomorphism of the associated mapping-cone
triangles. -/
instance triangleMap_isIso (sq : CommSq f a b g) [IsIso a] [IsIso b] :
    IsIso (triangleMap sq) := sorry

/-- The canonical isomorphism of module-level mapping-cone triangles attached to a square of
vertical isomorphisms. -/
noncomputable def triangleIso (sq : CommSq f a b g) [IsIso a] [IsIso b] :
    triangle f ≅ triangle g :=
  asIso (triangleMap sq)

/-- The hom of the canonical triangle isomorphism is the induced triangle map. -/
@[simp]
theorem triangleIso_hom (sq : CommSq f a b g) [IsIso a] [IsIso b] :
    (triangleIso sq).hom = triangleMap sq := sorry

/-- The homotopy-category image of a square of vertical isomorphisms induces an isomorphism of
mapping-cone triangles. -/
instance triangleMapK_isIso (sq : CommSq f a b g) [IsIso a] [IsIso b] :
    IsIso (triangleMapK sq) := sorry

/-- The canonical isomorphism of homotopy-category mapping-cone triangles attached to a square
of vertical isomorphisms. -/
noncomputable def triangleIsoK (sq : CommSq f a b g) [IsIso a] [IsIso b] :
    triangleK f ≅ triangleK g :=
  asIso (triangleMapK sq)

end

end SheafOfModules.RingedSite.DifferentialGradedModule.MappingCone
