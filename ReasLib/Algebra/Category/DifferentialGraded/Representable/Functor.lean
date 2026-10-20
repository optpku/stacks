module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Homotopy
public import ReasLib.Algebra.Category.DifferentialGraded.Representable
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy

/-!
# Enriched representable functors

For an object `x` of an `R`-linear differential graded category, homogeneous
postcomposition makes `y ↦ Hom(x, y)` a DG functor valued in right modules over
`End(x)`.  This is the reusable internal-Hom owner used by tensor-Hom adjunctions.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace DifferentialGradedCategory

variable {R : Type u} [CommRing R]
variable {C : Type v} [D : DifferentialGradedCategory.{u, v, w} R C]

open scoped DifferentialGradedCategory

/-- Homogeneous postcomposition applied to a representable homogeneous morphism. -/
def representableGradedMapValue (x : C) {y z : C} {j : ℤ}
    (g : y ⟶[j] z) (p : ℤ) (f : homComponent x y p) :
    homComponent x z (p + j) :=
  D.comp g f

/-- Homogeneous postcomposition as a graded morphism between representable right DG modules. -/
def representableGradedMap (x : C) {y z : C} {j : ℤ} (g : y ⟶[j] z) :
    DifferentialGradedModule.GradedHom (endomorphismDGA x)
      (representableModule x y) (representableModule x z) j :=
  ⟨fun p ↦
      { toFun := representableGradedMapValue x g p
        map_add' := sorry
        map_smul' := sorry },
    sorry⟩

/-- The enriched representable internal-Hom functor based at `x`, valued in right DG modules
over the endomorphism DGA `endomorphismDGA x`. -/
@[stacks 09LY "DG representable internal Hom functor"]
def representableDgFunctor (x : C) :
    DgFunctor R C
      (DifferentialGradedModule.{u, w} (endomorphismDGA x)) where
  obj y := representableModule x y
  map := representableGradedMap x
  map_add := sorry
  map_smul := sorry
  map_d := sorry
  map_id := sorry
  map_comp := sorry

/-- The enriched representable functor sends `y` to the explicit module `Hom(x, y)`. -/
@[simp]
theorem representableDgFunctor_obj (x y : C) :
    (representableDgFunctor x).obj y = representableModule x y := sorry

/-- The homogeneous map of the enriched representable functor is postcomposition. -/
@[simp]
theorem representableDgFunctor_map (x : C) {y z : C} {j : ℤ} (g : y ⟶[j] z) :
    (representableDgFunctor x).map g = representableGradedMap x g := sorry

/-- On closed degree-zero categories, the enriched representable functor is the ordinary
representable functor followed by the canonical closed presentation of DG modules. -/
theorem representableDgFunctor_mapComp (x : C) :
    (representableDgFunctor x).mapComp =
      representableFunctor x ⋙
        DifferentialGradedModule.toComp (endomorphismDGA x) := sorry

/-- On homotopy categories, the enriched representable functor still sends `y` to
`Hom(x, y)` with its right `endomorphismDGA x`-module structure. -/
@[simp]
theorem representableDgFunctor_mapK_obj (x : C) (y : K R C) :
    (representableDgFunctor x).mapK.obj y =
      (⟨representableModule x y.obj⟩ :
        K R (DifferentialGradedModule.{u, w} (endomorphismDGA x))) := sorry

/-- On a represented homotopy class, the enriched representable functor is represented by
homogeneous postcomposition. -/
@[simp]
theorem representableDgFunctor_mapK_map {x y z : C} (f : CompHom y z) :
    (representableDgFunctor x).mapK.map f.toHomotopyClass =
      (DgFunctor.mapCompHom (representableDgFunctor x) f).toHomotopyClass := sorry

end DifferentialGradedCategory
