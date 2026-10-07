module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import stacks_project.Chap65.Lemma_65_16_1_ChangeOfBase
public import stacks_project.Chap65.Lemma_65_16_3_Equivalence
public import stacks_project.Chap93.Example_93_11_1_Algebraic_spaces_Category

/-!
# Residue object and deformation category of an algebraic space

The object `x0 = (k, X)` of the residue fibre of `FlatAlgebraicSpaceCat.forget`,
and the slice `Def_X = F_{x0}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Functor

noncomputable section

universe u

namespace FlatAlgebraicSpaceCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The structure morphism `Spec(k) ⟶ Spec(Λ)`. -/
def residueBaseMap : Spec (CommRingCat.of k) ⟶ specBase Λ :=
  Spec.map (CommRingCat.ofHom (algebraMap Λ k))

/-- `residueBaseMap` is `Spec` of the structure map `Λ → k`. -/
theorem residueBaseMap_eq :
    residueBaseMap Λ k = Spec.map (CommRingCat.ofHom (algebraMap Λ k)) := sorry

/-- The object `x0 = (k, X)` of `F`, obtained by viewing an algebraic space over `k`
as a flat algebraic space over the residue object of `C_Λ`. -/
def ofResidue (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    FlatAlgebraicSpaceCat Λ k where
  base := ArtinianLocalAlgCat.residue Λ k
  space := extendBase (residueBaseMap Λ k) X
  structureHom := extendBaseHom (residueBaseMap Λ k) X
  isFlat := sorry

/-- The base of `ofResidue X` is the residue object of `C_Λ`. -/
theorem ofResidue_base (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    (ofResidue Λ k X).base = ArtinianLocalAlgCat.residue Λ k := sorry

/-- `x0 = (k, X)` as an object of the residue fibre of `forget`. -/
def residueObj (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    (forget Λ k).Fiber (ArtinianLocalAlgCat.residue Λ k) :=
  Fiber.mk (rfl : (forget Λ k).obj (ofResidue Λ k X) = ArtinianLocalAlgCat.residue Λ k)

/-- The residue-fibre object is included as `ofResidue X`. -/
theorem residueObj_fiberInclusion (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    Fiber.fiberInclusion.obj (residueObj Λ k X) = ofResidue Λ k X := sorry

/-- The deformation category `Def_X = F_{x0}` is the Over-slice at `x0 = (k, X)`. -/
abbrev deformation (X : AlgebraicSpace (Spec (CommRingCat.of k))) :=
  Over (Fiber.fiberInclusion.obj (residueObj Λ k X))

/-- `deformation X` is the Over-slice of the residue-fibre object `x0 = (k, X)`. -/
theorem deformation_spec (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    deformation Λ k X = Over (Fiber.fiberInclusion.obj (residueObj Λ k X)) := sorry

end FlatAlgebraicSpaceCat

