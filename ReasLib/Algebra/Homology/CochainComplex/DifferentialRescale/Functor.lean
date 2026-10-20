module

public import ReasLib.Algebra.Homology.CochainComplex.DifferentialRescale

/-!
# Functoriality of differential rescaling

Rescaling every differential of an integer-indexed cochain complex by a central unit is
functorial.  The resulting functor is canonically naturally isomorphic to the identity; in
degree `n`, the comparison is multiplication by `ε⁻ⁿ`.

@stack 0194
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u w

namespace CategoryTheory.CochainComplex

namespace rescaleDifferential

section Functor

variable {R : Type w} [Semiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- A cochain map still commutes with differentials after both complexes are rescaled by the
same scalar. -/
@[reassoc, stacks 0194 "cochain specialization rescaled map compatibility"]
theorem map_comm {K L : CochainComplex C ℤ}
    (r : R) (f : K ⟶ L) (i j : ℤ) :
    f.f i ≫ (L.rescaleDifferential r).d i j =
      (K.rescaleDifferential r).d i j ≫ f.f j := sorry

/-- A cochain map regarded as a map between complexes with equally rescaled differentials. -/
@[stacks 0194 "cochain specialization rescaled map"]
def map {K L : CochainComplex C ℤ}
    (r : R) (f : K ⟶ L) :
    K.rescaleDifferential r ⟶ L.rescaleDifferential r :=
  HomologicalComplex.Rescale.ofLinear.map (fun _ : ℤ ↦ r) f

/-- The cochain specialization does not change the components of a map. -/
@[simp, stacks 0194 "cochain specialization rescaled map component"]
theorem map_f {K L : CochainComplex C ℤ}
    (r : R) (f : K ⟶ L) (n : ℤ) :
    (map r f).f n = f.f n := sorry

/-- Rescaling sends an identity cochain map to an identity. -/
@[stacks 0194 "cochain specialization rescaling identity map"]
theorem map_id (r : R) (K : CochainComplex C ℤ) :
    map r (𝟙 K) = 𝟙 (K.rescaleDifferential r) := sorry

/-- Rescaling preserves composition of cochain maps. -/
@[stacks 0194 "cochain specialization rescaling composition"]
theorem map_comp (r : R)
    {K L M : CochainComplex C ℤ} (f : K ⟶ L) (g : L ⟶ M) :
    map r (f ≫ g) = map r f ≫ map r g := sorry

/-- Rescaling the differentials of integer-indexed cochain complexes by a fixed scalar. -/
@[stacks 0194 "cochain specialization rescaling functor"]
def functor (r : R) :
    CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  HomologicalComplex.Rescale.ofLinear.functor (C := C)
    (c := ComplexShape.up ℤ) (fun _ : ℤ ↦ r)

/-- The cochain rescaling functor has the expected object formula. -/
@[simp, stacks 0194 "cochain specialization rescaling functor object"]
theorem functor_obj (r : R) (K : CochainComplex C ℤ) :
    (functor (C := C) r).obj K = K.rescaleDifferential r := sorry

/-- The cochain rescaling functor has the expected map formula. -/
@[simp, stacks 0194 "cochain specialization rescaling functor map"]
theorem functor_map (r : R) {K L : CochainComplex C ℤ}
    (f : K ⟶ L) :
    (functor (C := C) r).map f = map r f := sorry

/-- The cochain rescaling functor leaves every map component unchanged. -/
@[simp, stacks 0194 "cochain specialization rescaling functor component"]
theorem functor_map_f (r : R) {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (n : ℤ) :
    ((functor (C := C) r).map f).f n = f.f n := sorry

end Functor

section Gauge

variable {R : Type w} [Semiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- The constant central-unit family used by cochain differential rescaling. -/
@[stacks 0194 "cochain rescaling central-unit family"]
def unitFamily (ε : Rˣ) : ℤ → (CatCenter C)ˣ :=
  fun _ ↦ Linear.toCatCenterUnits R C ε

/-- The degreewise potential which trivializes constant cochain rescaling. -/
@[stacks 0194 "cochain rescaling gauge potential"]
def potential (ε : Rˣ) : ℤ → (CatCenter C)ˣ :=
  fun n ↦ (Linear.toCatCenterUnits R C ε) ^ (-n)

/-- The potential recurrence for the upward cochain shape. -/
@[stacks 0194 "cochain rescaling gauge potential recurrence"]
theorem potential_isPotential (ε : Rˣ) :
    HomologicalComplex.Rescale.IsPotential (c := ComplexShape.up ℤ)
      (unitFamily (C := C) ε) (potential (C := C) ε) := sorry

/-- The degree-`n` comparison from a rescaled cochain complex to the original complex. -/
@[stacks 0194 "cochain specialization gauge component"]
noncomputable def component
    (K : CochainComplex C ℤ) (ε : Rˣ) (n : ℤ) :
    (K.rescaleDifferential (ε : R)).X n ≅ K.X n :=
  HomologicalComplex.Rescale.component K (unitFamily (C := C) ε)
    (potential (C := C) ε) n

/-- The degreewise rescaling comparisons commute with all differentials. -/
@[stacks 0194 "cochain specialization gauge compatibility"]
theorem component_comm
    (K : CochainComplex C ℤ) (ε : Rˣ) (i j : ℤ) :
    (component K ε i).hom ≫ K.d i j =
      (K.rescaleDifferential (ε : R)).d i j ≫
        (component K ε j).hom := sorry

/-- The forward cochain gauge component is the ordinary scalar action by `ε ^ (-n)`. -/
@[simp, stacks 0194 "cochain specialization gauge forward scalar action"]
theorem component_hom_smul (K : CochainComplex C ℤ) (ε : Rˣ) (n : ℤ) :
    (component K ε n).hom = ((ε ^ (-n) : Rˣ) : R) • 𝟙 _ := sorry

/-- The inverse cochain gauge component is the ordinary scalar action by `ε ^ n`. -/
@[simp, stacks 0194 "cochain specialization gauge inverse scalar action"]
theorem component_inv_smul (K : CochainComplex C ℤ) (ε : Rˣ) (n : ℤ) :
    (component K ε n).inv = ((ε ^ n : Rˣ) : R) • 𝟙 _ := sorry

/-- A complex with its differential rescaled by a unit is canonically isomorphic to the
original complex. -/
@[stacks 0194 "cochain specialization gauge isomorphism"]
noncomputable def iso
    (K : CochainComplex C ℤ) (ε : Rˣ) :
    K.rescaleDifferential (ε : R) ≅ K :=
  HomologicalComplex.Rescale.iso K (unitFamily (C := C) ε)
    (potential (C := C) ε) (potential_isPotential (C := C) ε)

/-- The canonical rescaling isomorphism is natural in the cochain complex. -/
@[reassoc, stacks 0194 "cochain specialization gauge naturality"]
theorem iso_hom_naturality
    {K L : CochainComplex C ℤ} (ε : Rˣ) (f : K ⟶ L) :
    map (ε : R) f ≫ (iso L ε).hom =
      (iso K ε).hom ≫ f := sorry

/-- The inverse cochain gauge comparison is natural in the rescaled complexes. -/
@[reassoc, stacks 0194 "cochain specialization inverse gauge naturality"]
theorem iso_inv_naturality
    {K L : CochainComplex C ℤ} (ε : Rˣ) (f : K ⟶ L) :
    f ≫ (iso L ε).inv =
      (iso K ε).inv ≫ map (ε : R) f := sorry

/-- The cochain gauge isomorphism has the named degreewise component. -/
@[simp, stacks 0194 "cochain specialization gauge forward component"]
theorem iso_hom_f (K : CochainComplex C ℤ) (ε : Rˣ) (n : ℤ) :
    (iso K ε).hom.f n =
      (component K ε n).hom := sorry

/-- The inverse cochain gauge isomorphism has the named degreewise component. -/
@[simp, stacks 0194 "cochain specialization gauge inverse component"]
theorem iso_inv_f (K : CochainComplex C ℤ) (ε : Rˣ) (n : ℤ) :
    (iso K ε).inv.f n =
      (component K ε n).inv := sorry

/-- The forward cochain gauge isomorphism component in ordinary scalar notation. -/
@[simp, stacks 0194 "cochain specialization gauge isomorphism scalar action"]
theorem iso_hom_f_smul (K : CochainComplex C ℤ) (ε : Rˣ) (n : ℤ) :
    (iso K ε).hom.f n = ((ε ^ (-n) : Rˣ) : R) • 𝟙 _ := sorry

/-- The inverse cochain gauge isomorphism component in ordinary scalar notation. -/
@[simp, stacks 0194 "cochain specialization inverse gauge isomorphism scalar action"]
theorem iso_inv_f_smul (K : CochainComplex C ℤ) (ε : Rˣ) (n : ℤ) :
    (iso K ε).inv.f n = ((ε ^ n : Rˣ) : R) • 𝟙 _ := sorry

/-- Differential rescaling by a unit is naturally isomorphic to the identity functor. -/
@[stacks 0194 "cochain specialization gauge natural isomorphism"]
noncomputable def natIso (ε : Rˣ) :
    functor (C := C) (ε : R) ≅ 𝟭 (CochainComplex C ℤ) :=
  HomologicalComplex.Rescale.natIso (C := C) (c := ComplexShape.up ℤ)
    (unitFamily (C := C) ε) (potential (C := C) ε)
    (potential_isPotential (C := C) ε)

/-- The cochain natural comparison evaluates to the named objectwise gauge isomorphism. -/
@[simp, stacks 0194 "cochain specialization gauge natural component"]
theorem natIso_app (ε : Rˣ) (K : CochainComplex C ℤ) :
    (natIso (C := C) ε).app K = iso K ε := sorry

/-- Rescaling cochain differentials by a scalar unit is an equivalence. -/
@[stacks 0194 "cochain specialization rescaling equivalence instance"]
noncomputable instance isEquivalence (ε : Rˣ) :
    (functor (C := C) (ε : R)).IsEquivalence := sorry

end Gauge

end rescaleDifferential

end CategoryTheory.CochainComplex
