/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.MappingCone
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Shift

/-!
# Mapping-cone triangles of differential graded module sheaves

This leaf supplies the canonical maps into and out of a differential graded mapping cone,
assembles the corresponding triangles before and after passage to the DG homotopy category,
and compares the underlying triangle with Mathlib's cochain-complex mapping-cone triangle.
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

namespace SheafOfModules.RingedSite.DifferentialGradedModule.MappingCone

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [HasBinaryBiproducts (ringedSiteModuleCategory J 𝒪)]
variable {𝒜 : DGA(𝒪)} {K L : Mod(𝒜, d)}

/-- The canonical inclusion of the target into the mapping cone. -/
noncomputable def inr (f : K ⟶ L) :
    L ⟶ _root_.SheafOfModules.RingedSite.DifferentialGradedModule.mappingCone f where
  toCochainMap :=
    { f := fun _ ↦ biprod.inl
      comm' := sorry }
  comm := sorry

/-- The mapping-cone inclusion is the first biproduct inclusion in every degree. -/
@[simp]
theorem inr_f (f : K ⟶ L) (n : ℤ) :
    (inr f).toCochainMap.f n =
      (biprod.inl : L.toComplex.X n ⟶
        L.toComplex.X n ⊞ K.toComplex.X (n + 1)) := sorry

/-- The canonical morphism from the mapping cone to the shift of its source. -/
noncomputable def toShift (f : K ⟶ L) :
    _root_.SheafOfModules.RingedSite.DifferentialGradedModule.mappingCone f ⟶
      Shift.obj K 1 where
  toCochainMap :=
    { f := fun _ ↦ -biprod.snd
      comm' := sorry }
  comm := sorry

/-- The map from the mapping cone to the shifted source is minus the second biproduct
projection in every degree. -/
@[simp]
theorem toShift_f (f : K ⟶ L) (n : ℤ) :
    (toShift f).toCochainMap.f n =
      -(biprod.snd :
        L.toComplex.X n ⊞ K.toComplex.X (n + 1) ⟶ K.toComplex.X (n + 1)) := sorry

/-- The cone inclusion followed by the projection to the shifted source is zero. -/
@[reassoc]
theorem inr_toShift (f : K ⟶ L) :
    inr f ≫ toShift f = 0 := sorry

/-- The mapping-cone triangle in the category of differential graded modules. -/
noncomputable def triangle (f : K ⟶ L) : Triangle Mod(𝒜, d) :=
  Triangle.mk f (inr f) (toShift f)

/-- The first object of the module-level mapping-cone triangle is the source. -/
@[simp]
theorem triangle_obj₁ (f : K ⟶ L) :
    (triangle f).obj₁ = K := sorry

/-- The second object of the module-level mapping-cone triangle is the target. -/
@[simp]
theorem triangle_obj₂ (f : K ⟶ L) :
    (triangle f).obj₂ = L := sorry

/-- The third object of the module-level mapping-cone triangle is the mapping cone. -/
@[simp]
theorem triangle_obj₃ (f : K ⟶ L) :
    (triangle f).obj₃ =
      _root_.SheafOfModules.RingedSite.DifferentialGradedModule.mappingCone f := sorry

/-- The underlying cochain-complex triangle is canonically isomorphic to Mathlib's standard
mapping-cone triangle. -/
noncomputable def underlyingTriangleIso (f : K ⟶ L) :
    (forgetToComplex 𝒜).mapTriangle.obj (triangle f) ≅
      CochainComplex.mappingCone.triangle f.toCochainMap :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (_root_.SheafOfModules.RingedSite.DifferentialGradedModule.mappingConeToCochainMappingCone f)
    sorry sorry sorry

/-- The mapping-cone triangle in the DG homotopy category. -/
noncomputable def triangleK (f : K ⟶ L) :
    Triangle (DifferentialGradedCategory.K ℤ Mod(𝒜, d)) :=
  (toK 𝒜).mapTriangle.obj (triangle f)

/-- The first object of the homotopy-category mapping-cone triangle is represented by the
source module. -/
@[simp]
theorem triangleK_obj₁ (f : K ⟶ L) :
    (triangleK f).obj₁ = ⟨K⟩ := sorry

/-- The second object of the homotopy-category mapping-cone triangle is represented by the
target module. -/
@[simp]
theorem triangleK_obj₂ (f : K ⟶ L) :
    (triangleK f).obj₂ = ⟨L⟩ := sorry

/-- The third object of the homotopy-category mapping-cone triangle is represented by the
mapping cone. -/
@[simp]
theorem triangleK_obj₃ (f : K ⟶ L) :
    (triangleK f).obj₃ =
      ⟨_root_.SheafOfModules.RingedSite.DifferentialGradedModule.mappingCone f⟩ := sorry

/-- The first morphism of the homotopy-category mapping-cone triangle is the image of `f`. -/
@[simp]
theorem triangleK_mor₁ (f : K ⟶ L) :
    (triangleK f).mor₁ = (toK 𝒜).map f := sorry

/-- The second morphism of the homotopy-category mapping-cone triangle is the image of the
canonical cone inclusion. -/
@[simp]
theorem triangleK_mor₂ (f : K ⟶ L) :
    (triangleK f).mor₂ = (toK 𝒜).map (inr f) := sorry

/-- The third morphism of the homotopy-category mapping-cone triangle is the cone projection
followed by the shift comparison for `toK`. -/
@[simp]
theorem triangleK_mor₃ (f : K ⟶ L) :
    (triangleK f).mor₃ =
      (toK 𝒜).map (toShift f) ≫
        ((toK 𝒜).commShiftIso (1 : ℤ)).hom.app K := sorry

end

end SheafOfModules.RingedSite.DifferentialGradedModule.MappingCone
