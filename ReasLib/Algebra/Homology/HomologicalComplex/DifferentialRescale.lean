module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Center.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Degreewise rescaling of homological differentials

This file rescales the differential of an arbitrary homological complex by a scalar depending on
the source degree. It also packages the resulting functor and the gauge comparison supplied by a
compatible family of central units. Chain and cochain sign conventions are specializations of
this source-degree construction.

@stack 0194
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u t

namespace CategoryTheory.HomologicalComplex

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]
variable {ι : Type t} {c : ComplexShape ι}

section Core

/-- A source-degree scalar family preserves the shape-zero equations of a homological complex. -/
@[stacks 0194 "source-degree differential rescaling shape law"]
theorem rescale_shape (K : HomologicalComplex C c) (s : ι → CatCenter C)
    (i j : ι) (hij : ¬ c.Rel i j) :
    s i • K.d i j = 0 := sorry

/-- Source-degree scalar rescaling preserves the square-zero equations of a homological complex. -/
@[stacks 0194 "source-degree differential rescaling square-zero law"]
theorem rescale_d_comp_d (K : HomologicalComplex C c) (s : ι → CatCenter C)
    (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k) :
    (s i • K.d i j) ≫ (s j • K.d j k) = 0 := sorry

/-- The homological complex obtained by multiplying the differential out of degree `i` by
`s i`. -/
@[stacks 0194 "source-degree differential rescaling"]
def rescale (K : HomologicalComplex C c) (s : ι → CatCenter C) :
    HomologicalComplex C c where
  X := K.X
  d i j := s i • K.d i j
  shape := rescale_shape K s
  d_comp_d' := rescale_d_comp_d K s

/-- Source-degree differential rescaling leaves every object unchanged. -/
@[simp, stacks 0194 "source-degree differential rescaling object formula"]
theorem rescale_X (K : HomologicalComplex C c) (s : ι → CatCenter C) (i : ι) :
    (rescale K s).X i = K.X i := sorry

/-- The rescaled differential is the prescribed source-degree scalar multiple. -/
@[simp, stacks 0194 "source-degree differential rescaling formula"]
theorem rescale_d (K : HomologicalComplex C c) (s : ι → CatCenter C) (i j : ι) :
    (rescale K s).d i j = s i • K.d i j := sorry

namespace Rescale

/-- A homological map commutes with equally rescaled differentials. -/
@[reassoc, stacks 0194 "source-degree rescaled map compatibility"]
theorem map_comm {K L : HomologicalComplex C c} (s : ι → CatCenter C)
    (f : K ⟶ L) (i j : ι) :
    f.f i ≫ (rescale L s).d i j =
      (rescale K s).d i j ≫ f.f j := sorry

/-- A homological map regarded as a map between equally rescaled complexes. -/
@[stacks 0194 "source-degree rescaled homological map"]
def map {K L : HomologicalComplex C c} (s : ι → CatCenter C) (f : K ⟶ L) :
    rescale K s ⟶ rescale L s where
  f := f.f
  comm' i j _ := map_comm s f i j

/-- Rescaling does not change the component of a homological map in any degree. -/
@[simp, stacks 0194 "source-degree rescaled homological map component"]
theorem map_f {K L : HomologicalComplex C c} (s : ι → CatCenter C)
    (f : K ⟶ L) (i : ι) :
    (map s f).f i = f.f i := sorry

/-- Rescaling preserves identity homological maps. -/
@[simp, stacks 0194 "source-degree rescaling identity map"]
theorem map_id (s : ι → CatCenter C) (K : HomologicalComplex C c) :
    map s (𝟙 K) = 𝟙 (rescale K s) := sorry

/-- Rescaling preserves composition of homological maps. -/
@[stacks 0194 "source-degree rescaling composition"]
theorem map_comp (s : ι → CatCenter C) {K L M : HomologicalComplex C c}
    (f : K ⟶ L) (g : L ⟶ M) :
    map s (f ≫ g) = map s f ≫ map s g := sorry

/-- Rescaling homological differentials by a fixed source-degree scalar family. -/
@[stacks 0194 "source-degree differential rescaling functor"]
def functor (s : ι → CatCenter C) :
    HomologicalComplex C c ⥤ HomologicalComplex C c where
  obj K := rescale K s
  map f := map s f
  map_id K := map_id s K
  map_comp f g := map_comp s f g

/-- The object formula for the source-degree differential rescaling functor. -/
@[simp, stacks 0194 "source-degree rescaling functor object"]
theorem functor_obj (s : ι → CatCenter C) (K : HomologicalComplex C c) :
    (functor (C := C) (c := c) s).obj K = rescale K s := sorry

/-- The map formula for the source-degree differential rescaling functor. -/
@[simp, stacks 0194 "source-degree rescaling functor map"]
theorem functor_map (s : ι → CatCenter C)
    {K L : HomologicalComplex C c} (f : K ⟶ L) :
    (functor (C := C) (c := c) s).map f = map s f := sorry

/-- The rescaling functor preserves the component formula for every homological map. -/
@[simp, stacks 0194 "source-degree rescaling functor component"]
theorem functor_map_f (s : ι → CatCenter C)
    {K L : HomologicalComplex C c} (f : K ⟶ L) (i : ι) :
    ((functor (C := C) (c := c) s).map f).f i = f.f i := sorry

end Rescale

end Core

namespace Rescale

namespace Units

/-- The underlying central scalar family of a family of central units. -/
@[stacks 0194 "central scalar family of units"]
def scalar (s : ι → (CatCenter C)ˣ) : ι → CatCenter C := fun i ↦ (s i : CatCenter C)

omit [Limits.HasZeroMorphisms C] in
/-- Evaluation of the central scalar family is the underlying central unit. -/
@[simp, stacks 0194 "central scalar family evaluation"]
theorem scalar_apply (s : ι → (CatCenter C)ˣ) (i : ι) :
    scalar s i = (s i : CatCenter C) := sorry

/-- The pointwise scalar family of the inverse unit family. -/
@[stacks 0194 "inverse central scalar family"]
def invScalar (s : ι → (CatCenter C)ˣ) : ι → CatCenter C :=
  scalar (fun i ↦ (s i)⁻¹)

omit [Limits.HasZeroMorphisms C] in
/-- Evaluation of the inverse central scalar family. -/
@[simp, stacks 0194 "inverse central scalar family evaluation"]
theorem invScalar_apply (s : ι → (CatCenter C)ˣ) (i : ι) :
    invScalar s i = ((s i)⁻¹).val := sorry

/-- Rescaling a homological complex by a family of central units. -/
@[stacks 0194 "unit-family source-degree rescaling"]
def obj (K : HomologicalComplex C c) (s : ι → (CatCenter C)ˣ) :
    HomologicalComplex C c :=
  rescale K (scalar s)

/-- The functorial source-degree rescaling by a family of central units. -/
@[stacks 0194 "unit-family source-degree rescaling functor"]
def functor (s : ι → (CatCenter C)ˣ) :
    HomologicalComplex C c ⥤ HomologicalComplex C c :=
  Rescale.functor (scalar s)

/-- A homological map regarded as a map between two unit-rescaled complexes. -/
@[stacks 0194 "unit-family rescaled homological map"]
def map {K L : HomologicalComplex C c} (s : ι → (CatCenter C)ˣ) (f : K ⟶ L) :
    obj K s ⟶ obj L s :=
  Rescale.map (scalar s) f

/-- Unit-family rescaling leaves every graded object unchanged. -/
@[simp, stacks 0194 "unit-family rescaling object formula"]
theorem obj_X (K : HomologicalComplex C c) (s : ι → (CatCenter C)ˣ) (i : ι) :
    (obj K s).X i = K.X i := sorry

/-- Unit-family rescaling multiplies the differential by the source-degree unit. -/
@[simp, stacks 0194 "unit-family rescaling differential formula"]
theorem obj_d (K : HomologicalComplex C c) (s : ι → (CatCenter C)ˣ) (i j : ι) :
    (obj K s).d i j = scalar s i • K.d i j := sorry

/-- The object formula for the unit-family rescaling functor. -/
@[simp, stacks 0194 "unit-family rescaling functor object formula"]
theorem functor_obj (s : ι → (CatCenter C)ˣ) (K : HomologicalComplex C c) :
    (functor (C := C) (c := c) s).obj K = obj K s := sorry

/-- A map is unchanged componentwise by unit-family rescaling. -/
@[simp, stacks 0194 "unit-family rescaling functor map formula"]
theorem functor_map (s : ι → (CatCenter C)ˣ)
    {K L : HomologicalComplex C c} (f : K ⟶ L) :
    (functor (C := C) (c := c) s).map f = map s f := sorry

/-- The unit-family rescaling functor preserves map components degreewise. -/
@[simp, stacks 0194 "unit-family rescaling functor component"]
theorem functor_map_f (s : ι → (CatCenter C)ˣ)
    {K L : HomologicalComplex C c} (f : K ⟶ L) (i : ι) :
    ((functor (C := C) (c := c) s).map f).f i = f.f i := sorry

/-- The component formula for a unit-family rescaled map. -/
@[simp, stacks 0194 "unit-family rescaled homological map component"]
theorem map_f {K L : HomologicalComplex C c} (s : ι → (CatCenter C)ˣ)
    (f : K ⟶ L) (i : ι) :
    (map s f).f i = f.f i := sorry

/-- A unit-family rescaled map commutes with the rescaled differentials. -/
@[reassoc, stacks 0194 "unit-family rescaled map compatibility"]
theorem map_comm {K L : HomologicalComplex C c} (s : ι → (CatCenter C)ˣ)
    (f : K ⟶ L) (i j : ι) :
    f.f i ≫ (obj L s).d i j = (obj K s).d i j ≫ f.f j := sorry

/-- The identity formula for unit-family rescaled maps. -/
@[simp, stacks 0194 "unit-family rescaled homological map identity"]
theorem map_id (s : ι → (CatCenter C)ˣ) (K : HomologicalComplex C c) :
    map s (𝟙 K) = 𝟙 (obj K s) := sorry

/-- The composition formula for unit-family rescaled maps. -/
@[stacks 0194 "unit-family rescaled homological map composition"]
theorem map_comp (s : ι → (CatCenter C)ˣ)
    {K L M : HomologicalComplex C c} (f : K ⟶ L) (g : L ⟶ M) :
    map s (f ≫ g) = map s f ≫ map s g := sorry

namespace one

/-- The identity components commute with the constant-one rescaled differential. -/
@[stacks 0194 "unit-family rescaling unit compatibility"]
theorem iso_comm (K : HomologicalComplex C c) (i j : ι) :
    (Iso.refl _).hom ≫ K.d i j =
      (obj K (fun _ : ι ↦ 1)).d i j ≫ (Iso.refl _).hom := sorry

/-- Rescaling by the constant unit family is canonically isomorphic to the original complex. -/
@[stacks 0194 "unit-family rescaling unit object comparison"]
noncomputable def iso (K : HomologicalComplex C c) :
    obj K (fun _ ↦ 1) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _)
    (fun i j _ ↦ iso_comm K i j)

/-- The forward map of the constant-one comparison is the identity in every degree. -/
@[simp, stacks 0194 "unit-family rescaling unit forward component"]
theorem iso_hom_f (K : HomologicalComplex C c) (i : ι) :
    (iso K).hom.f i = 𝟙 _ := sorry

/-- The inverse map of the constant-one comparison is the identity in every degree. -/
@[simp, stacks 0194 "unit-family rescaling unit inverse component"]
theorem iso_inv_f (K : HomologicalComplex C c) (i : ι) :
    (iso K).inv.f i = 𝟙 _ := sorry

/-- The constant-one comparison is natural in the homological complex. -/
@[reassoc, stacks 0194 "unit-family rescaling unit naturality"]
theorem iso_naturality {K L : HomologicalComplex C c} (f : K ⟶ L) :
    (functor (C := C) (c := c) (fun _ : ι ↦ 1)).map f ≫ (iso L).hom =
      (iso K).hom ≫ f := sorry

/-- Rescaling by the constant unit family is naturally isomorphic to the identity functor. -/
@[stacks 0194 "unit-family rescaling unit comparison"]
noncomputable def natIso :
    functor (C := C) (c := c) (fun _ ↦ 1) ≅
      𝟭 (HomologicalComplex C c) :=
  NatIso.ofComponents (fun K ↦ iso K) (fun f ↦ iso_naturality f)

/-- The object component of the constant-one comparison. -/
@[simp, stacks 0194 "unit-family rescaling unit component"]
theorem natIso_app (K : HomologicalComplex C c) :
    (natIso (C := C) (c := c)).app K = iso K := sorry

end one

namespace mul

/-- Identity components intertwine successive rescaling with pointwise multiplication. -/
@[stacks 0194 "unit-family rescaling multiplication compatibility"]
theorem iso_comm (K : HomologicalComplex C c) (s t : ι → (CatCenter C)ˣ)
    (i j : ι) :
    (Iso.refl _).hom ≫ (obj K (fun k ↦ t k * s k)).d i j =
      (obj (obj K s) t).d i j ≫ (Iso.refl _).hom := sorry

/-- Two successive unit-family rescalings combine by pointwise multiplication, with the outer
family multiplying the inner family. -/
@[stacks 0194 "unit-family rescaling multiplication object comparison"]
noncomputable def iso (K : HomologicalComplex C c) (s t : ι → (CatCenter C)ˣ) :
    obj (obj K s) t ≅ obj K (fun i ↦ t i * s i) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _)
    (fun i j _ ↦ iso_comm K s t i j)

/-- The forward multiplication comparison is the identity in every degree. -/
@[simp, stacks 0194 "unit-family rescaling multiplication forward component"]
theorem iso_hom_f (K : HomologicalComplex C c) (s t : ι → (CatCenter C)ˣ) (i : ι) :
    (iso K s t).hom.f i = 𝟙 _ := sorry

/-- The inverse multiplication comparison is the identity in every degree. -/
@[simp, stacks 0194 "unit-family rescaling multiplication inverse component"]
theorem iso_inv_f (K : HomologicalComplex C c) (s t : ι → (CatCenter C)ˣ) (i : ι) :
    (iso K s t).inv.f i = 𝟙 _ := sorry

/-- The pointwise multiplication comparison is natural in the homological complex. -/
@[reassoc, stacks 0194 "unit-family rescaling multiplication naturality"]
theorem iso_naturality (s t : ι → (CatCenter C)ˣ)
    {K L : HomologicalComplex C c} (f : K ⟶ L) :
    (functor (C := C) (c := c) s ⋙ functor (C := C) (c := c) t).map f ≫
        (iso L s t).hom =
      (iso K s t).hom ≫
        (functor (C := C) (c := c) (fun i ↦ t i * s i)).map f := sorry

/-- Pointwise multiplication is the composition law for unit-family rescaling functors. -/
@[stacks 0194 "unit-family rescaling multiplication comparison"]
noncomputable def natIso (s t : ι → (CatCenter C)ˣ) :
    functor (C := C) (c := c) s ⋙ functor (C := C) (c := c) t ≅
      functor (C := C) (c := c) (fun i ↦ t i * s i) :=
  NatIso.ofComponents (fun K ↦ iso K s t) (fun f ↦ iso_naturality s t f)

/-- The object component of the pointwise multiplication comparison. -/
@[simp, stacks 0194 "unit-family rescaling multiplication component"]
theorem natIso_app (s t : ι → (CatCenter C)ˣ) (K : HomologicalComplex C c) :
    (natIso (C := C) (c := c) s t).app K = iso K s t := sorry

end mul

namespace compInv

/-- Identity components intertwine a unit rescaling followed by its pointwise inverse. -/
@[stacks 0194 "inverse unit-family rescaling compatibility"]
theorem iso_comm (K : HomologicalComplex C c) (s : ι → (CatCenter C)ˣ)
    (i j : ι) :
    (Iso.refl _).hom ≫ K.d i j =
      (obj (obj K s) (fun k ↦ (s k)⁻¹)).d i j ≫ (Iso.refl _).hom := sorry

/-- A unit rescaling followed by its pointwise inverse is isomorphic to the identity. -/
@[stacks 0194 "inverse unit-family rescaling object comparison"]
noncomputable def iso (K : HomologicalComplex C c) (s : ι → (CatCenter C)ˣ) :
    obj (obj K s) (fun i ↦ (s i)⁻¹) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _)
    (fun i j _ ↦ iso_comm K s i j)

/-- The forward unit-then-inverse comparison is the identity in every degree. -/
@[simp, stacks 0194 "inverse unit-family rescaling forward component"]
theorem iso_hom_f (K : HomologicalComplex C c) (s : ι → (CatCenter C)ˣ) (i : ι) :
    (iso K s).hom.f i = 𝟙 _ := sorry

/-- The inverse unit-then-inverse comparison is the identity in every degree. -/
@[simp, stacks 0194 "inverse unit-family rescaling inverse component"]
theorem iso_inv_f (K : HomologicalComplex C c) (s : ι → (CatCenter C)ˣ) (i : ι) :
    (iso K s).inv.f i = 𝟙 _ := sorry

/-- The unit-then-inverse comparison is natural in the homological complex. -/
@[reassoc, stacks 0194 "inverse unit-family rescaling naturality"]
theorem iso_naturality (s : ι → (CatCenter C)ˣ)
    {K L : HomologicalComplex C c} (f : K ⟶ L) :
    (functor (C := C) (c := c) s ⋙
        functor (C := C) (c := c) (fun i ↦ (s i)⁻¹)).map f ≫ (iso L s).hom =
      (iso K s).hom ≫ f := sorry

/-- The unit-then-inverse comparison is natural in the complex. -/
@[stacks 0194 "inverse unit-family rescaling comparison"]
noncomputable def natIso (s : ι → (CatCenter C)ˣ) :
    functor (C := C) (c := c) s ⋙
        functor (C := C) (c := c) (fun i ↦ (s i)⁻¹) ≅
      𝟭 (HomologicalComplex C c) :=
  NatIso.ofComponents (fun K ↦ iso K s) (fun f ↦ iso_naturality s f)

/-- The object component of the unit-then-inverse comparison. -/
@[simp, stacks 0194 "inverse unit-family comparison component"]
theorem natIso_app (s : ι → (CatCenter C)ˣ) (K : HomologicalComplex C c) :
    (natIso (C := C) (c := c) s).app K = iso K s := sorry

end compInv

namespace invComp

/-- Identity components intertwine an inverse-unit rescaling followed by the original family. -/
@[stacks 0194 "inverse-first unit-family rescaling compatibility"]
theorem iso_comm (K : HomologicalComplex C c) (s : ι → (CatCenter C)ˣ)
    (i j : ι) :
    (Iso.refl _).hom ≫ K.d i j =
      (obj (obj K (fun k ↦ (s k)⁻¹)) s).d i j ≫ (Iso.refl _).hom := sorry

/-- An inverse-unit rescaling followed by the original family is isomorphic to the identity. -/
@[stacks 0194 "inverse-first unit-family rescaling object comparison"]
noncomputable def iso (K : HomologicalComplex C c) (s : ι → (CatCenter C)ˣ) :
    obj (obj K (fun i ↦ (s i)⁻¹)) s ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _)
    (fun i j _ ↦ iso_comm K s i j)

/-- The forward inverse-then-unit comparison is the identity in every degree. -/
@[simp, stacks 0194 "inverse-first unit-family rescaling forward component"]
theorem iso_hom_f (K : HomologicalComplex C c) (s : ι → (CatCenter C)ˣ) (i : ι) :
    (iso K s).hom.f i = 𝟙 _ := sorry

/-- The inverse inverse-then-unit comparison is the identity in every degree. -/
@[simp, stacks 0194 "inverse-first unit-family rescaling inverse component"]
theorem iso_inv_f (K : HomologicalComplex C c) (s : ι → (CatCenter C)ˣ) (i : ι) :
    (iso K s).inv.f i = 𝟙 _ := sorry

/-- The inverse-then-unit comparison is natural in the homological complex. -/
@[reassoc, stacks 0194 "inverse-first unit-family rescaling naturality"]
theorem iso_naturality (s : ι → (CatCenter C)ˣ)
    {K L : HomologicalComplex C c} (f : K ⟶ L) :
    (functor (C := C) (c := c) (fun i ↦ (s i)⁻¹) ⋙
        functor (C := C) (c := c) s).map f ≫ (iso L s).hom =
      (iso K s).hom ≫ f := sorry

/-- The inverse-then-unit comparison is natural in the complex. -/
@[stacks 0194 "inverse-first unit-family rescaling comparison"]
noncomputable def natIso (s : ι → (CatCenter C)ˣ) :
    functor (C := C) (c := c) (fun i ↦ (s i)⁻¹) ⋙
        functor (C := C) (c := c) s ≅
      𝟭 (HomologicalComplex C c) :=
  NatIso.ofComponents (fun K ↦ iso K s) (fun f ↦ iso_naturality s f)

/-- The object component of the inverse-then-unit comparison. -/
@[simp, stacks 0194 "inverse-first unit-family comparison component"]
theorem natIso_app (s : ι → (CatCenter C)ˣ) (K : HomologicalComplex C c) :
    (natIso (C := C) (c := c) s).app K = iso K s := sorry

end invComp

/-- Every unit-family rescaling is an equivalence, with pointwise inverse family as quasi-inverse. -/
@[stacks 0194 "unit-family rescaling equivalence instance"]
instance isEquivalence (s : ι → (CatCenter C)ˣ) :
    (functor (C := C) (c := c) s).IsEquivalence := sorry

end Units

open Units

section Gauge

/-- A unit potential whose ratio across every allowed differential equals the chosen
source-degree rescaling unit. -/
@[stacks 0194 "source-degree rescaling unit potential"]
def IsPotential (s a : ι → (CatCenter C)ˣ) : Prop :=
  ∀ i j, c.Rel i j → a i = s i * a j

namespace IsPotential

omit [Limits.HasZeroMorphisms C] in
/-- The constant unit family is a potential for itself. -/
@[stacks 0194 "unit potential identity"]
theorem one :
    IsPotential (c := c)
      (fun _ : ι ↦ (1 : (CatCenter C)ˣ))
      (fun _ : ι ↦ (1 : (CatCenter C)ˣ)) := sorry

omit [Limits.HasZeroMorphisms C] in
/-- Potentials multiply pointwise, compatibly with composition of rescaling families. -/
@[stacks 0194 "unit potential multiplication"]
theorem mul {s t a b : ι → (CatCenter C)ˣ}
    (ha : IsPotential (c := c) s a) (hb : IsPotential (c := c) t b) :
    IsPotential (c := c) (fun i ↦ t i * s i) (fun i ↦ b i * a i) := sorry

omit [Limits.HasZeroMorphisms C] in
/-- A pointwise inverse potential trivializes the pointwise inverse rescaling family. -/
@[stacks 0194 "unit potential inversion"]
theorem inv {s a : ι → (CatCenter C)ˣ} (ha : IsPotential (c := c) s a) :
    IsPotential (c := c) (fun i ↦ (s i)⁻¹) (fun i ↦ (a i)⁻¹) := sorry

end IsPotential

/-- The degreewise gauge isomorphism from a unit-rescaled complex to the original complex. -/
@[stacks 0194 "source-degree rescaling gauge component"]
noncomputable def component (K : HomologicalComplex C c)
    (s a : ι → (CatCenter C)ˣ) (i : ι) :
    (Units.obj K s).X i ≅ K.X i :=
  a i • Iso.refl _

/-- Compatible gauge components intertwine the rescaled and original differentials. -/
@[reassoc, stacks 0194 "source-degree rescaling gauge compatibility"]
theorem component_comm (K : HomologicalComplex C c)
    (s a : ι → (CatCenter C)ˣ)
    (ha : IsPotential (c := c) s a) (i j : ι) :
    (component K s a i).hom ≫ K.d i j =
      (Units.obj K s).d i j ≫ (component K s a j).hom := sorry

/-- The forward component of a gauge is the central-unit action. -/
@[simp, stacks 0194 "source-degree gauge component forward action"]
theorem component_hom (K : HomologicalComplex C c)
    (s a : ι → (CatCenter C)ˣ) (i : ι) :
    (component K s a i).hom = scalar a i • 𝟙 _ := sorry

/-- The inverse component of a gauge is the inverse central-unit action. -/
@[simp, stacks 0194 "source-degree gauge component inverse action"]
theorem component_inv (K : HomologicalComplex C c)
    (s a : ι → (CatCenter C)ˣ) (i : ι) :
    (component K s a i).inv = invScalar a i • 𝟙 _ := sorry

/-- A compatible unit potential identifies a source-rescaled complex with the original one. -/
@[stacks 0194 "source-degree differential rescaling gauge isomorphism"]
noncomputable def iso (K : HomologicalComplex C c)
    (s a : ι → (CatCenter C)ˣ)
    (ha : IsPotential (c := c) s a) :
    Units.obj K s ≅ K :=
  HomologicalComplex.Hom.isoOfComponents
    (component K s a) (fun i j _ ↦ component_comm K s a ha i j)

/-- The forward component of the gauge isomorphism is the prescribed central-unit action. -/
@[simp, stacks 0194 "source-degree gauge forward component"]
theorem iso_hom_f (K : HomologicalComplex C c)
    (s a : ι → (CatCenter C)ˣ)
    (ha : IsPotential (c := c) s a) (i : ι) :
    (iso K s a ha).hom.f i = (component K s a i).hom := sorry

/-- The inverse component of the gauge isomorphism is the inverse central-unit action. -/
@[simp, stacks 0194 "source-degree gauge inverse component"]
theorem iso_inv_f (K : HomologicalComplex C c)
    (s a : ι → (CatCenter C)ˣ)
    (ha : IsPotential (c := c) s a) (i : ι) :
    (iso K s a ha).inv.f i = (component K s a i).inv := sorry

/-- Gauge isomorphisms are natural in the underlying homological complex. -/
@[reassoc, stacks 0194 "source-degree gauge naturality"]
theorem iso_hom_naturality {K L : HomologicalComplex C c}
    (s a : ι → (CatCenter C)ˣ)
    (ha : IsPotential (c := c) s a) (f : K ⟶ L) :
    Units.map s f ≫ (iso L s a ha).hom =
      (iso K s a ha).hom ≫ f := sorry

/-- Gauge isomorphisms satisfy the inverse naturality equation as well. -/
@[reassoc, stacks 0194 "source-degree inverse gauge naturality"]
theorem iso_inv_naturality {K L : HomologicalComplex C c}
    (s a : ι → (CatCenter C)ˣ)
    (ha : IsPotential (c := c) s a) (f : K ⟶ L) :
    f ≫ (iso L s a ha).inv =
      (iso K s a ha).inv ≫ Units.map s f := sorry

/-- A compatible source-degree unit rescaling is naturally isomorphic to the identity functor. -/
@[stacks 0194 "source-degree differential rescaling natural isomorphism"]
noncomputable def natIso (s a : ι → (CatCenter C)ˣ)
    (ha : IsPotential (c := c) s a) :
    Units.functor (C := C) (c := c) s ≅
      𝟭 (HomologicalComplex C c) :=
  NatIso.ofComponents (fun K ↦ iso K s a ha)
    (fun f ↦ iso_hom_naturality s a ha f)

/-- The object component of the gauge natural isomorphism is the named gauge isomorphism. -/
@[simp, stacks 0194 "source-degree gauge natural component"]
theorem natIso_app (s a : ι → (CatCenter C)ˣ)
    (ha : IsPotential (c := c) s a) (K : HomologicalComplex C c) :
    (natIso (C := C) (c := c) s a ha).app K = iso K s a ha := sorry

end Gauge

end Rescale

end CategoryTheory.HomologicalComplex
