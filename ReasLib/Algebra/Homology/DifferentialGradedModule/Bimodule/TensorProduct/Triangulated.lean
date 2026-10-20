/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Triangulated
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.Shift
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Shift.Category
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Triangulated

/-!
# Triangulated Tensoring by a Differential Graded Bimodule

The explicit shift comparison for relative tensor product supplies the global shift
compatibility instance for its functor on DG homotopy categories.  Triangulatedness then follows
from the generic theorem for DG functors.
-/

@[expose] public section

noncomputable section

universe u v w x y

open CategoryTheory
open DifferentialGradedCategory

namespace DifferentialGradedBimodule.Tensor

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, x} R} {B : CochainDGAlgebra.{u, y} R}

/-- The pointwise tensor-shift isomorphism in the DG homotopy category. -/
@[stacks 09LR "pointwise tensor shift isomorphism"]
def mapKShiftIsoApp (N : DifferentialGradedBimodule.{u, w, x, y} A B)
    (M : K R (DifferentialGradedModule.{u, v} A)) (k : ℤ) :
    ((DifferentialGradedModule.Shift.K.functor A k ⋙
        (dgFunctor N).mapK).obj M) ≅
      (((dgFunctor N).mapK ⋙
        DifferentialGradedModule.Shift.K.functor B k).obj M) :=
  (DifferentialGradedModule.toK B).mapIso (shiftIso N M.obj k).symm

/-- The pointwise tensor-shift isomorphisms are natural on the DG homotopy category. -/
@[stacks 09LR "naturality of the pointwise tensor shift isomorphism"]
theorem mapKShiftIso_naturality (N : DifferentialGradedBimodule.{u, w, x, y} A B) (k : ℤ)
    {M M' : K R (DifferentialGradedModule.{u, v} A)} (f : M ⟶ M') :
    (DifferentialGradedModule.Shift.K.functor A k ⋙ (dgFunctor N).mapK).map f ≫
        (mapKShiftIsoApp N M' k).hom =
      (mapKShiftIsoApp N M k).hom ≫
        ((dgFunctor N).mapK ⋙
          DifferentialGradedModule.Shift.K.functor B k).map f := sorry

/-- Tensoring by a fixed DG bimodule commutes naturally with the explicit shifts on DG
homotopy categories. -/
@[stacks 09LR "tensor shift isomorphism"]
def mapKShiftIso (N : DifferentialGradedBimodule.{u, w, x, y} A B) (k : ℤ) :
    DifferentialGradedModule.Shift.K.functor A k ⋙ (dgFunctor N).mapK ≅
      (dgFunctor N).mapK ⋙ DifferentialGradedModule.Shift.K.functor B k :=
  NatIso.ofComponents (fun M ↦ mapKShiftIsoApp N M k)
    (fun f ↦ mapKShiftIso_naturality N k f)

/-- The global tensor shift isomorphism has the canonical pointwise hom component. -/
@[simp, stacks 09LR "tensor shift isomorphism hom component"]
theorem mapKShiftIso_hom_app (N : DifferentialGradedBimodule.{u, w, x, y} A B)
    (M : K R (DifferentialGradedModule.{u, v} A)) (k : ℤ) :
    (mapKShiftIso N k).hom.app M = Iso.hom (mapKShiftIsoApp N M k) := sorry

/-- The global tensor shift isomorphism has the canonical pointwise inverse component. -/
@[simp, stacks 09LR "tensor shift isomorphism inverse component"]
theorem mapKShiftIso_inv_app (N : DifferentialGradedBimodule.{u, w, x, y} A B)
    (M : K R (DifferentialGradedModule.{u, v} A)) (k : ℤ) :
    (mapKShiftIso N k).inv.app M = Iso.inv (mapKShiftIsoApp N M k) := sorry

/-- Tensoring by a fixed DG bimodule commutes with the canonical abstract shifts on DG
homotopy categories. -/
@[stacks 09LR "canonical shift comparison for relative tensoring"]
def mapKCommShiftIso (N : DifferentialGradedBimodule.{u, w, x, y} A B) (k : ℤ) :
    shiftFunctor (K R (DifferentialGradedModule.{u, v} A)) k ⋙ (dgFunctor N).mapK ≅
      (dgFunctor N).mapK ⋙
        shiftFunctor (K R (DifferentialGradedModule.{u, max v w} B)) k :=
  (Functor.isoWhiskerRight
      (eqToIso (DifferentialGradedModule.Shift.K.shiftFunctor_eq A k))
      ((dgFunctor N).mapK)).trans
    ((mapKShiftIso N k).trans
      (Functor.isoWhiskerLeft ((dgFunctor N).mapK)
        (eqToIso (DifferentialGradedModule.Shift.K.shiftFunctor_eq B k).symm)))

/-- The canonical tensor-shift comparison agrees with the zero-shift comparison. -/
theorem mapKCommShiftIso_zero (N : DifferentialGradedBimodule.{u, w, x, y} A B) :
    mapKCommShiftIso N 0 = Functor.CommShift.isoZero (dgFunctor N).mapK ℤ := sorry

/-- The canonical tensor-shift comparison is compatible with addition of shifts. -/
theorem mapKCommShiftIso_add (N : DifferentialGradedBimodule.{u, w, x, y} A B) (i j : ℤ) :
    mapKCommShiftIso N (i + j) =
      Functor.CommShift.isoAdd (mapKCommShiftIso N i) (mapKCommShiftIso N j) := sorry

/-- Remark 22.29.2 (0FQN): the homotopy functor induced by tensoring with a fixed DG bimodule
has a canonical global shift-compatibility instance. -/
@[stacks 0FQN "relative tensor product is triangulated on homotopy categories"]
noncomputable instance mapKCommShift (N : DifferentialGradedBimodule.{u, w, x, y} A B) :
    (dgFunctor N).mapK.CommShift ℤ where
  commShiftIso := mapKCommShiftIso N
  commShiftIso_zero := mapKCommShiftIso_zero N
  commShiftIso_add := mapKCommShiftIso_add N

/-- Lemma 22.33.1 (09LR): tensoring with a fixed differential graded bimodule induces a
triangulated functor on homotopy categories. -/
@[stacks 09LR]
noncomputable instance mapK_isTriangulated (N : DifferentialGradedBimodule.{u, w, x, y} A B) :
    (dgFunctor N).mapK.IsTriangulated := sorry

section

variable (N : DifferentialGradedBimodule.{u, w, x, y} A B)

#synth (dgFunctor.{u, v, w, x, y} N).mapK.CommShift ℤ
#synth (dgFunctor.{u, v, w, x, y} N).mapK.IsTriangulated

end

end DifferentialGradedBimodule.Tensor
