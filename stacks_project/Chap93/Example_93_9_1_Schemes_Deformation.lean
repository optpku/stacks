module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import stacks_project.Chap90.Remark_90_6_4
public import stacks_project.Chap93.Example_93_9_1_Schemes_Category

/-!
# Deformation category of a scheme

The residue object `x0 = (k, X)` of a scheme over `k`, and the slice
`Def_X = F_{x0}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

universe u

namespace FlatSchemeCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The residue object `x0 = (k, X)` of a scheme flat over `k`. -/
def ofResidue (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] : FlatSchemeCat Λ k :=
  of (ArtinianLocalAlgCat.residue Λ k) X hX

/-- The forgetful image of `ofResidue X hX` is the residue object of `C_Λ`. -/
theorem ofResidue_base (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    (ofResidue Λ k X hX).base = ArtinianLocalAlgCat.residue Λ k := sorry

/-- `x0 = (k, X)` as an object of the residue fibre of `forget`. -/
def residueObj (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    (forget Λ k).Fiber (ArtinianLocalAlgCat.residue Λ k) :=
  Fiber.mk (rfl : (forget Λ k).obj (ofResidue Λ k X hX) = ArtinianLocalAlgCat.residue Λ k)

/-- The residue-fibre object is included as `ofResidue X hX`. -/
theorem residueObj_fiberInclusion (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    Fiber.fiberInclusion.obj (residueObj Λ k X hX) = ofResidue Λ k X hX := sorry

/-- The deformation category `Def_X` is the slice `F_{x0}` at `x0 = (k, X)`. -/
abbrev deformationCategory (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :=
  Over (Fiber.fiberInclusion.obj (residueObj Λ k X hX))

/-- `deformationCategory X hX` is the Over-slice of the residue-fibre object `x0`. -/
theorem deformationCategory_spec (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    deformationCategory Λ k X hX =
      Over (Fiber.fiberInclusion.obj (residueObj Λ k X hX)) := sorry

/-- The slice projection `p_{x0} : F_{x0} ⥤ C_Λ` is a predeformation category. -/
instance instIsPredeformationCategory_deformationCategory
    (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    IsPredeformationCategory
      (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X hX)) ⋙ forget Λ k) :=
  inferInstance

end FlatSchemeCat
