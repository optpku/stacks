module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import ReasLib.Algebra.Homology.DifferentialGradedModule.MappingCone.Homotopy
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Shift.Category

/-!
# Mapping-Cone Triangles of Differential Graded Modules

This leaf assembles the explicit mapping cone into a triangle of right differential graded modules
and then into a triangle in the DG homotopy category.  Strictly and homotopy-commutative squares
receive compatible, concrete triangle morphisms.
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

/-- The standard third map of a mapping-cone triangle is minus the projection to the shifted
source. -/
def toShift (f : K ⟶ L) : mappingCone f ⟶ shift K 1 :=
  -projection f

/-- The third mapping-cone map is degreewise minus the second-coordinate projection. -/
@[simp] theorem toShift_hom (f : K ⟶ L) (n : ℤ) :
    (toShift f).hom n = -LinearMap.snd R (L.X n) (K.X (n + 1)) := sorry

/-- The inclusion into a mapping cone followed by its map to the shifted source is zero. -/
@[reassoc] theorem inclusion_toShift (f : K ⟶ L) :
    inclusion f ≫ toShift f = 0 := sorry

/-- The mapping-cone triangle in the category of right differential graded modules. -/
def triangle (f : K ⟶ L) : Triangle (DifferentialGradedModule.{u, v} A) :=
  Triangle.mk f (inclusion f) (toShift f)

/-- The first object of the module-level mapping-cone triangle is its source. -/
@[simp] theorem triangle_obj₁ (f : K ⟶ L) : (triangle f).obj₁ = K := sorry

/-- The second object of the module-level mapping-cone triangle is its target. -/
@[simp] theorem triangle_obj₂ (f : K ⟶ L) : (triangle f).obj₂ = L := sorry

/-- The third object of the module-level mapping-cone triangle is the explicit mapping cone. -/
@[simp] theorem triangle_obj₃ (f : K ⟶ L) : (triangle f).obj₃ = mappingCone f := sorry

/-- The first morphism of the module-level mapping-cone triangle is the original map. -/
@[simp] theorem triangle_mor₁ (f : K ⟶ L) : (triangle f).mor₁ = f := sorry

/-- The second morphism of the module-level mapping-cone triangle is the target inclusion. -/
@[simp] theorem triangle_mor₂ (f : K ⟶ L) :
    (triangle f).mor₂ = inclusion f := sorry

/-- The third morphism of the module-level mapping-cone triangle is minus the source projection. -/
@[simp] theorem triangle_mor₃ (f : K ⟶ L) :
    (triangle f).mor₃ = toShift f := sorry

/-- A strictly commutative square induces a morphism of module-level mapping-cone triangles. -/
def triangleMap {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, v} A}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂} (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : f₁ ≫ b = a ≫ f₂) : triangle f₁ ⟶ triangle f₂ where
  hom₁ := a
  hom₂ := b
  hom₃ := map a b comm
  comm₁ := sorry
  comm₂ := sorry
  comm₃ := sorry

/-- The first component of a strict mapping-cone triangle map is the source map. -/
@[simp] theorem triangleMap_hom₁
    {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, v} A}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂} (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : f₁ ≫ b = a ≫ f₂) :
    (triangleMap a b comm).hom₁ = a := sorry

/-- The second component of a strict mapping-cone triangle map is the target map. -/
@[simp] theorem triangleMap_hom₂
    {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, v} A}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂} (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : f₁ ≫ b = a ≫ f₂) :
    (triangleMap a b comm).hom₂ = b := sorry

/-- The third component of a strict mapping-cone triangle map is the block-diagonal cone map. -/
@[simp] theorem triangleMap_hom₃
    {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, v} A}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂} (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : f₁ ≫ b = a ≫ f₂) :
    (triangleMap a b comm).hom₃ = map a b comm := sorry

/-- The mapping-cone triangle in the DG homotopy category. -/
def triangleK (f : K ⟶ L) :
    Triangle (DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A)) :=
  (toK A).mapTriangle.obj (triangle f)

/-- The first object of the homotopy-category cone triangle is represented by the source. -/
@[simp] theorem triangleK_obj₁ (f : K ⟶ L) : (triangleK f).obj₁ = ⟨K⟩ := sorry

/-- The second object of the homotopy-category cone triangle is represented by the target. -/
@[simp] theorem triangleK_obj₂ (f : K ⟶ L) : (triangleK f).obj₂ = ⟨L⟩ := sorry

/-- The third object of the homotopy-category cone triangle is represented by the mapping cone. -/
@[simp] theorem triangleK_obj₃ (f : K ⟶ L) :
    (triangleK f).obj₃ = ⟨mappingCone f⟩ := sorry

/-- The first morphism of the homotopy-category cone triangle is the image of the original map. -/
@[simp] theorem triangleK_mor₁ (f : K ⟶ L) :
    (triangleK f).mor₁ = (toK A).map f := sorry

/-- The second morphism of the homotopy-category cone triangle is the image of the inclusion. -/
@[simp] theorem triangleK_mor₂ (f : K ⟶ L) :
    (triangleK f).mor₂ = (toK A).map (inclusion f) := sorry

/-- The third morphism of the homotopy-category cone triangle is the image of `toShift` followed
by the canonical shift comparison. -/
@[simp] theorem triangleK_mor₃ (f : K ⟶ L) :
    (triangleK f).mor₃ =
      (toK A).map (toShift f) ≫ ((toK A).commShiftIso (1 : ℤ)).hom.app K := sorry

/-- The morphism of cone triangles in the DG homotopy category induced by a strict square. -/
def triangleMapK {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, v} A}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂} (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : f₁ ≫ b = a ≫ f₂) : triangleK f₁ ⟶ triangleK f₂ :=
  (toK A).mapTriangle.map (triangleMap a b comm)

/-- Lemma 22.6.2 (09KD): a homotopy-commutative square of right differential graded module maps
induces the explicit morphism between their mapping-cone triangles in the DG homotopy category. -/
@[stacks 09KD]
def triangleMapKOfHomotopy
    {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, v} A}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂} {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂}
    (H : Homotopy (f₁ ≫ b) (a ≫ f₂)) : triangleK f₁ ⟶ triangleK f₂ where
  hom₁ := (toK A).map a
  hom₂ := (toK A).map b
  hom₃ := (toK A).map (mapOfHomotopy H)
  comm₁ := sorry
  comm₂ := sorry
  comm₃ := sorry

/-- The first component of the triangle map induced by a homotopy is the source map in `K`. -/
@[simp] theorem triangleMapKOfHomotopy_hom₁
    {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, v} A}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂} {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂}
    (H : Homotopy (f₁ ≫ b) (a ≫ f₂)) :
    (triangleMapKOfHomotopy H).hom₁ = (toK A).map a := sorry

/-- The second component of the triangle map induced by a homotopy is the target map in `K`. -/
@[simp] theorem triangleMapKOfHomotopy_hom₂
    {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, v} A}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂} {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂}
    (H : Homotopy (f₁ ≫ b) (a ≫ f₂)) :
    (triangleMapKOfHomotopy H).hom₂ = (toK A).map b := sorry

/-- The third component of the triangle map induced by a homotopy is represented by the explicit
upper-triangular map of cones. -/
@[simp] theorem triangleMapKOfHomotopy_hom₃
    {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, v} A}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂} {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂}
    (H : Homotopy (f₁ ≫ b) (a ≫ f₂)) :
    (triangleMapKOfHomotopy H).hom₃ = (toK A).map (mapOfHomotopy H) := sorry

/-- A strict cone-triangle map agrees with the homotopy-induced map for the zero homotopy. -/
theorem triangleMapK_eq_ofEq
    {K₁ L₁ K₂ L₂ : DifferentialGradedModule.{u, v} A}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂} (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : f₁ ≫ b = a ≫ f₂) :
    triangleMapK a b comm = triangleMapKOfHomotopy (Homotopy.ofEq comm) := sorry

end DifferentialGradedModule.MappingCone
