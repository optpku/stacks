module

public import ReasLib.Algebra.Homology.HomologicalComplex.DifferentialRescale
public import ReasLib.CategoryTheory.Center.Linear

/-!
# Linear scalar specializations of differential rescaling

The shape-generic rescaling API is expressed using the categorical center.  This leaf supplies
the canonical bridge for a linear category: a scalar family is sent to its central natural
endomorphism, and all object, map, and functor constructions are inherited from `Rescale`.

@stack 0194
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u w t

namespace CategoryTheory.HomologicalComplex.Rescale

variable {R : Type w} [Semiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
variable {ι : Type t} {c : ComplexShape ι}

namespace ofLinear

/-- The central family associated to a linear scalar family. -/
@[stacks 0194 "linear central scalar family"]
def scalar (s : ι → R) : ι → CatCenter C :=
  fun i ↦ CategoryTheory.Linear.scalarCenter R C (s i)

/-- The component of the central family associated to a scalar. -/
@[simp, stacks 0194 "linear central scalar component"]
theorem scalar_app (s : ι → R) (i : ι) (X : C) :
    (scalar (C := C) s i).app X = s i • 𝟙 X := sorry

/-- The action of the central family associated to a scalar is the linear action. -/
@[simp, stacks 0194 "linear central scalar action"]
theorem scalar_smul (s : ι → R) (i : ι) {X Y : C} (f : X ⟶ Y) :
    scalar (C := C) s i • f = s i • f := sorry

end ofLinear

/-- A scalar family acts on a homological complex through the categorical center. -/
@[stacks 0194 "linear source-degree differential rescaling"]
def ofLinear (K : HomologicalComplex C c) (s : ι → R) :
    HomologicalComplex C c :=
  rescale K (ofLinear.scalar (C := C) s)

/-- The graded objects are unchanged by linear scalar rescaling. -/
@[simp, stacks 0194 "linear source-degree rescaling object formula"]
theorem ofLinear_X (K : HomologicalComplex C c) (s : ι → R) (i : ι) :
    (ofLinear K s).X i = K.X i := sorry

/-- The differential of a linearly rescaled complex is the prescribed scalar multiple. -/
@[simp, stacks 0194 "linear source-degree rescaling differential formula"]
theorem ofLinear_d (K : HomologicalComplex C c) (s : ι → R) (i j : ι) :
    (ofLinear K s).d i j = s i • K.d i j := sorry

namespace ofLinear

/-- The linear bridge is the generic center-valued rescaling with its canonical scalar family. -/
@[stacks 0194 "linear rescaling definition bridge"]
theorem def_eq (K : HomologicalComplex C c) (s : ι → R) :
    ofLinear K s = CategoryTheory.HomologicalComplex.rescale K
      (scalar (C := C) s) := sorry

/-- A homological map is transported through a common linear scalar rescaling. -/
@[stacks 0194 "linear source-degree rescaled map"]
def map {K L : HomologicalComplex C c} (s : ι → R) (f : K ⟶ L) :
    ofLinear K s ⟶ ofLinear L s :=
  Rescale.map (scalar (C := C) s) f

/-- Linear scalar rescaling does not change map components. -/
@[simp, stacks 0194 "linear source-degree rescaled map component"]
theorem map_f {K L : HomologicalComplex C c} (s : ι → R) (f : K ⟶ L) (i : ι) :
    (map s f).f i = f.f i := sorry

/-- Linear scalar rescaling maps commute with differentials in every pair of degrees. -/
@[reassoc, stacks 0194 "linear source-degree rescaled map compatibility"]
theorem map_comm {K L : HomologicalComplex C c} (s : ι → R) (f : K ⟶ L)
    (i j : ι) :
    f.f i ≫ (ofLinear L s).d i j = (ofLinear K s).d i j ≫ f.f j := sorry

/-- Linear scalar rescaling preserves identity maps. -/
@[stacks 0194 "linear source-degree rescaling identity map"]
theorem map_id (s : ι → R) (K : HomologicalComplex C c) :
    map s (𝟙 K) = 𝟙 (ofLinear K s) := sorry

/-- Linear scalar rescaling preserves composition of maps. -/
@[stacks 0194 "linear source-degree rescaling composition"]
theorem map_comp (s : ι → R) {K L M : HomologicalComplex C c}
    (f : K ⟶ L) (g : L ⟶ M) :
    map s (f ≫ g) = map s f ≫ map s g := sorry

/-- The functor induced by a linear scalar family on homological complexes. -/
@[stacks 0194 "linear source-degree rescaling functor"]
def functor (s : ι → R) :
    HomologicalComplex C c ⥤ HomologicalComplex C c :=
  Rescale.functor (ofLinear.scalar (C := C) s)

/-- The object formula for the linear scalar rescaling functor. -/
@[simp, stacks 0194 "linear source-degree rescaling functor object"]
theorem functor_obj (s : ι → R) (K : HomologicalComplex C c) :
    (functor (C := C) (c := c) s).obj K = ofLinear K s := sorry

/-- The map formula for the linear scalar rescaling functor. -/
@[simp, stacks 0194 "linear source-degree rescaling functor map"]
theorem functor_map (s : ι → R) {K L : HomologicalComplex C c} (f : K ⟶ L) :
    (functor (C := C) (c := c) s).map f = map s f := sorry

/-- The component formula for a map under the linear scalar rescaling functor. -/
@[simp, stacks 0194 "linear source-degree rescaling functor component"]
theorem functor_map_f (s : ι → R) {K L : HomologicalComplex C c}
    (f : K ⟶ L) (i : ι) :
    ((functor (C := C) (c := c) s).map f).f i = f.f i := sorry

end ofLinear

end CategoryTheory.HomologicalComplex.Rescale
