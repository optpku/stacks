/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.RationalMap.ComponentStalk
public import ReasLib.AlgebraicGeometry.Scheme.Variety.RationalMap
public import ReasLib.FieldTheory.Extension.Category

/-!
# Function fields of varieties and finitely generated extensions

This file relates varieties with dominant rational maps to finitely generated
field extensions through the function-field construction.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.VarietyDominantRationalMapCat

variable {k : Type u} [Field k]

/-- The affine scheme over `k` obtained from the finite-type subalgebra selected inside a
finitely generated field extension. -/
noncomputable def affineModel (K : FinitelyGeneratedFieldExtension.Cat k) :
    SchemeOverField k :=
  let A : Subalgebra k K.obj :=
    @Algebra.EssFiniteType.subalgebra k K.obj _ _ _ K.property.2
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A)))

/-- The affine model of a finitely generated field extension is a variety over `k`. -/
theorem affineModel_isVariety (K : FinitelyGeneratedFieldExtension.Cat k) :
    Variety (affineModel K) := sorry

/-- The affine model, bundled as an object of the dominant rational-map category. -/
noncomputable def affineModelObject (K : FinitelyGeneratedFieldExtension.Cat k) :
    VarietyDominantRationalMapCat k :=
  ⟨affineModel K, affineModel_isVariety K⟩

/-- The function field of the affine model is isomorphic, as a `k`-algebra, to the given
finitely generated field extension. -/
theorem functionField_affineModel_equiv (K : FinitelyGeneratedFieldExtension.Cat k) :
    Nonempty
      (SchemeOverField.functionFieldCommAlg (affineModelObject K).obj ≅ K.obj) := sorry

/-- Varieties over `k` with dominant rational maps are equivalent to the opposite category of
finitely generated field extensions of `k`. -/
theorem nonemptyEquivFinitelyGeneratedFieldExtensions :
    Nonempty
      (VarietyDominantRationalMapCat k ≌ (FinitelyGeneratedFieldExtension.Cat k)ᵒᵖ) := sorry

end AlgebraicGeometry.VarietyDominantRationalMapCat
