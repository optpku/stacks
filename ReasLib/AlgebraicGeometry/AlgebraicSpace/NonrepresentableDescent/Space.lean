/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

@[expose] public section

open CategoryTheory Limits Opposite
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
  (hdeg : Module.finrank k k' = 2)

/-- The canonical projection from the quadratic cover to its small étale quotient. -/
def spaceAtlas :
    yoneda.obj (cover k k') ⟶ (preRelation k k' hdeg).smallEtaleQuotientSheaf.obj :=
  (preRelation k k' hdeg).smallEtaleQuotientSheafMk

/-- The small étale quotient of the quadratic Galois relation satisfies fppf descent. -/
theorem smallQuotient_isSheaf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over (base k))
      (preRelation k k' hdeg).smallEtaleQuotientSheaf.obj := by
  sorry

/-- The diagonal of the quadratic Galois quotient is representable by schemes. -/
theorem smallQuotient_representableDiagonal :
    yoneda.relativelyRepresentable
      (Limits.diag (preRelation k k' hdeg).smallEtaleQuotientSheaf.obj) := by
  sorry

/-- The canonical projection to the quadratic Galois quotient is representable and étale. -/
theorem smallQuotient_atlas_etale :
    (MorphismProperty.over (@Etale)).presheaf (spaceAtlas k k' hdeg) :=
  ⟨Functor.relativelyRepresentable.of_diag
    (smallQuotient_representableDiagonal k k' hdeg) (spaceAtlas k k' hdeg), by sorry⟩

/-- The canonical projection to the quadratic Galois quotient is étale-locally surjective. -/
instance smallQuotient_atlas_locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k))
      (spaceAtlas k k' hdeg) := by
  sorry

/-- The algebraic space obtained by quotienting the affine line over a quadratic Galois
extension by the diagonal and the punctured Galois graph. -/
def space : AlgebraicSpace (base k) :=
  ofFunctor (preRelation k k' hdeg).smallEtaleQuotientSheaf.obj
    (smallQuotient_isSheaf k k' hdeg) (smallQuotient_representableDiagonal k k' hdeg)
    ⟨cover k k', spaceAtlas k k' hdeg, smallQuotient_atlas_etale k k' hdeg,
      smallQuotient_atlas_locallySurjective k k' hdeg⟩

/-- The functor of points of the quadratic quotient is its small étale quotient sheaf. -/
theorem space_functorOfPoints :
    (space k k' hdeg).functorOfPoints =
      (preRelation k k' hdeg).smallEtaleQuotientSheaf.obj := rfl

/-- The structure morphism of the quadratic quotient sends each section to the structure
map of its test scheme over the affine line. -/
def spaceStructureHom : space k k' hdeg ⟶ ofOver (baseAsOver k) where
  app T := TypeCat.ofHom (fun _ ↦ toBaseAsOver k T.unop)
  naturality := by
    intro T T' f
    ext x
    apply Over.OverMorphism.ext
    change (toBaseAsOver k T'.unop).left =
      f.unop.left ≫ (toBaseAsOver k T.unop).left
    rw [toBaseAsOver_left, toBaseAsOver_left]
    exact (Over.w f.unop).symm

/-- Every component of the structure morphism is the unique map to the base over itself. -/
theorem spaceStructureHom_app (T : Over (base k))
    (x : (space k k' hdeg).functorOfPoints.obj (op T)) :
    (spaceStructureHom k k' hdeg).app (op T) x = toBaseAsOver k T := rfl

end AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent
