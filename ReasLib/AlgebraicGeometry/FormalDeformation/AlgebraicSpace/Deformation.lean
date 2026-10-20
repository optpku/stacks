module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase
public import ReasLib.AlgebraicGeometry.FormalDeformation.AlgebraicSpace.Category

/-!
# Residue objects and deformations of algebraic spaces

An algebraic space over the residue field determines an object of the residue
fiber of the category of flat algebraic spaces. Its deformation category is
the category of arrows into that object.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Functor Opposite TypeCat

noncomputable section

universe u

namespace FlatAlgebraicSpaceCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The spectrum structure morphism induced by the residue-field algebra. -/
def residueBaseMap : Spec (CommRingCat.of k) ⟶ specBase Λ :=
  Spec.map (CommRingCat.ofHom (algebraMap Λ k))

/-- The residue structure morphism is the spectrum of the algebra map to the residue field. -/
theorem residueBaseMap_eq :
    residueBaseMap Λ k = Spec.map (CommRingCat.ofHom (algebraMap Λ k)) := sorry

/-- The structure morphism of a residue-field space extended to the base projects its coproduct index. -/
def residueStructureHom (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    extendBase (residueBaseMap Λ k) X ⟶ specObj (ArtinianLocalAlgCat.residue Λ k) where
  app testScheme := ofHom fun sectionData ↦ sectionData.1
  naturality := sorry

/-- The component of the residue structure morphism returns the chosen lift of the base map. -/
theorem residueStructureHom_app (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    {testScheme : Over (specBase Λ)} (φ : testScheme ⟶ Over.mk (residueBaseMap Λ k))
    (sectionData : X.functorOfPoints.obj (op (Over.mk φ.left))) :
    (residueStructureHom Λ k X).app (op testScheme) ⟨φ, sectionData⟩ = φ := sorry

/-- An algebraic space over the residue field, viewed as a flat space over the residue algebra. -/
def ofResidue (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    FlatAlgebraicSpaceCat Λ k :=
  of (ArtinianLocalAlgCat.residue Λ k) (extendBase (residueBaseMap Λ k) X)
    (residueStructureHom Λ k X) sorry

/-- The base of a residue-field space is the canonical residue algebra. -/
theorem ofResidue_base (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    (ofResidue Λ k X).base = ArtinianLocalAlgCat.residue Λ k := sorry

/-- An algebraic space over the residue field defines an object of the residue fiber. -/
def residueObj (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    (forget Λ k).Fiber (ArtinianLocalAlgCat.residue Λ k) :=
  Fiber.mk (rfl : (forget Λ k).obj (ofResidue Λ k X) = ArtinianLocalAlgCat.residue Λ k)

/-- The inclusion of the residue-fiber object is its underlying flat algebraic space. -/
theorem residueObj_fiberInclusion (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    Fiber.fiberInclusion.obj (residueObj Λ k X) = ofResidue Λ k X := sorry

/-- The deformation category of a residue-field algebraic space is the category of arrows into it. -/
abbrev deformation (X : AlgebraicSpace (Spec (CommRingCat.of k))) :=
  Over (Fiber.fiberInclusion.obj (residueObj Λ k X))

/-- The deformation category is the over category at the included residue-fiber object. -/
theorem deformation_spec (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    deformation Λ k X = Over (Fiber.fiberInclusion.obj (residueObj Λ k X)) := sorry

end FlatAlgebraicSpaceCat
