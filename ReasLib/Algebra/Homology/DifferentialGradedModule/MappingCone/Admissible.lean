module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible.Triangle
public import ReasLib.Algebra.Homology.DifferentialGradedModule.MappingCone.Triangle

/-!
# The Admissible Short Exact Sequence of a Mapping Cone

The standard maps `L ⟶ mappingCone f ⟶ K[1]` form a short complex which is split after
forgetting the differential but retaining the graded right action.  This file owns the explicit
graded retraction and section, so downstream constructions can use the cone row without choosing
a splitting.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Pretriangulated DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedModule.MappingCone

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra R}
variable {K L : DifferentialGradedModule.{u, v} A}

/-- The canonical short complex `L ⟶ mappingCone f ⟶ K[1]`. -/
def shortComplex (f : K ⟶ L) :
    CategoryTheory.ShortComplex (DifferentialGradedModule.{u, v} A) where
  f := inclusion f
  g := projection f
  zero := sorry

/-- The first map in the cone short complex is the target inclusion. -/
@[simp]
theorem shortComplex_f (f : K ⟶ L) : (shortComplex f).f = inclusion f := sorry

/-- The second map in the cone short complex is the shifted-source projection. -/
@[simp]
theorem shortComplex_g (f : K ⟶ L) : (shortComplex f).g = projection f := sorry

/-- The graded retraction of the target inclusion is projection to the first cone coordinate. -/
def gradedRetraction (f : K ⟶ L) :
    Graded.Hom (mappingCone f).toGraded L.toGraded where
  hom n := LinearMap.fst R (L.X n) (K.X (n + 1))
  comm_smul := sorry

/-- The graded section of the shifted-source projection is inclusion into the second cone
coordinate. -/
def gradedSection (f : K ⟶ L) :
    Graded.Hom (K[1]).toGraded (mappingCone f).toGraded where
  hom n := LinearMap.inr R (L.X n) (K.X (n + 1))
  comm_smul := sorry

/-- The cone-row graded retraction is the first-coordinate projection in every degree. -/
@[simp]
theorem gradedRetraction_hom (f : K ⟶ L) (n : ℤ) :
    (gradedRetraction f).hom n = LinearMap.fst R (L.X n) (K.X (n + 1)) := sorry

/-- The cone-row graded section is the second-coordinate inclusion in every degree. -/
@[simp]
theorem gradedSection_hom (f : K ⟶ L) (n : ℤ) :
    (gradedSection f).hom n = LinearMap.inr R (L.X n) (K.X (n + 1)) := sorry

/-- The canonical graded `A`-linear splitting of the cone short complex. -/
@[stacks 09KB "graded splitting of the mapping-cone short exact sequence"]
def gradedSplitting (f : K ⟶ L) :
    ShortComplex.GradedSplitting (shortComplex f) where
  r := gradedRetraction f
  s := gradedSection f
  f_r := sorry
  s_g := sorry
  id := sorry

/-- The cone short complex is short exact. -/
theorem shortExact (f : K ⟶ L) : (shortComplex f).ShortExact := sorry

/-- The cone short exact sequence is admissible after retaining the graded `A`-module action. -/
theorem isAdmissibleShortExact (f : K ⟶ L) :
    DifferentialGradedModule.IsAdmissibleShortExact (shortComplex f) := sorry

/-- The connecting morphism of the canonical cone splitting is `f[1]`. -/
theorem connectingHom_eq (f : K ⟶ L) :
    (gradedSplitting f).connectingHom = shiftMap f 1 := sorry

/-- Lemma 22.9.1 (09KB): the triangle associated to the cone short exact sequence is
`(L, mappingCone f, K[1], inclusion f, projection f, shiftMap f 1)`. -/
@[stacks 09KB]
theorem associatedTriangle_eq (f : K ⟶ L) :
    ShortComplex.associatedTriangle (shortComplex f) (gradedSplitting f) =
      Triangle.mk (inclusion f) (projection f) (shiftMap f 1) := sorry

/-- In the intrinsic DG homotopy category, the cone-row associated triangle is the image of its
explicit module-level presentation. -/
theorem associatedTriangleK_eq (f : K ⟶ L) :
    ShortComplex.associatedTriangleK (shortComplex f) (gradedSplitting f) =
      (toK A).mapTriangle.obj
        (Triangle.mk (inclusion f) (projection f) (shiftMap f 1)) := sorry

end DifferentialGradedModule.MappingCone
