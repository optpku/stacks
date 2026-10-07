module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Order.Hom.Basic
public import ReasLib.CategoryTheory.Filtration.Complex.Finite
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Support
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Total.Support

/-!
# Filtrations on the Total Complex of a Double Complex

This file constructs the two standard decreasing filtrations on the total complex of a
cohomological double complex.  The filtration stages are explicit images of cutoff endomorphisms,
so the resulting filtered complexes are reusable independently of any chosen associated spectral
sequence.

The association between a filtered complex and a spectral sequence remains an explicit
proposition.  It is therefore passed to convergence results as data rather than installed as a
typeclass instance.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe u v w₁ w₂ w

namespace HomologicalComplex₂

section FilteredTotal

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]

section Axis

/-- The endomorphism retaining bidegrees above an integer-valued monotone axis cutoff. -/
@[stacks 0130 "axis cutoff on a filtered total complex"]
noncomputable abbrev Total.Filtration.cutoff (axis : ℤ × ℤ →o ℤ) (n p : ℤ) :
    (K.total (up ℤ)).X n ⟶ (K.total (up ℤ)).X n :=
  Total.Support.cutoff K (fun ij ↦ p ≤ axis ij) n

/-- The axis cutoff is identity on retained total-complex summands and zero otherwise. -/
@[stacks 0130 "axis cutoff on total-complex summands", reassoc (attr := simp)]
theorem Total.Filtration.ι_cutoff (axis : ℤ × ℤ →o ℤ) (n p i j : ℤ)
    (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = n) :
    K.ιTotal (up ℤ) i j n h ≫ Total.Filtration.cutoff K axis n p =
      if p ≤ axis (i, j) then K.ιTotal (up ℤ) i j n h else 0 := sorry

section HasImages

variable [HasImages C]

/-- The image subobject at an integer axis cutoff. -/
@[stacks 0130 "axis stage of a filtered total complex"]
noncomputable abbrev Total.Filtration.stage (axis : ℤ × ℤ →o ℤ) (n p : ℤ) :
    Subobject ((K.total (up ℤ)).X n) :=
  Total.Support.stage K (fun ij ↦ p ≤ axis ij) n

/-- Increasing the cutoff decreases every axis stage. -/
theorem Total.Filtration.stage_antitone (axis : ℤ × ℤ →o ℤ) (n : ℤ) :
    Antitone (fun p : ℤ ↦ Total.Filtration.stage K axis n p) := sorry

/-- Axis stages are monotone when the cutoff is indexed by `ℤᵒᵈ`. -/
theorem Total.Filtration.stage_monotone (axis : ℤ × ℤ →o ℤ) (n : ℤ) :
    Monotone (fun p : ℤᵒᵈ ↦ Total.Filtration.stage K axis n (OrderDual.ofDual p)) := sorry

/-- A total degree equipped with the filtration cut out by an integer-valued axis. -/
@[stacks 0130 "axis-filtered total object"]
noncomputable def Total.Filtration.object (axis : ℤ × ℤ →o ℤ) (n : ℤ) : FilteredObject C where
  obj := (K.total (up ℤ)).X n
  filtration :=
    { toFun := fun p ↦ Total.Filtration.stage K axis n (OrderDual.ofDual p)
      monotone' := Total.Filtration.stage_monotone K axis n }

end HasImages

end Axis

section AxisComplex

variable [HasImages C]

/-- The total differential preserves every stage cut out by a monotone axis. -/
theorem Total.Filtration.differential_preserves
    (axis : ℤ × ℤ →o ℤ) (i j : ℤ) :
    ∀ p : ℤ,
      ((Total.Filtration.object K axis j).filtration.stage p).Factors
        (((Total.Filtration.object K axis i).filtration.stage p).arrow ≫
          (K.total (up ℤ)).d i j) := sorry

/-- The differential between axis-filtered total degrees. -/
@[stacks 0130 "axis-filtered total differential"]
noncomputable def Total.Filtration.differential
    (axis : ℤ × ℤ →o ℤ)
    (i j : ℤ) : Total.Filtration.object K axis i ⟶ Total.Filtration.object K axis j where
  hom := (K.total (up ℤ)).d i j
  preserves := Total.Filtration.differential_preserves K axis i j

/-- The axis-filtered differential vanishes away from the cochain-complex shape. -/
theorem Total.Filtration.differential_shape
    (axis : ℤ × ℤ →o ℤ)
    (i j : ℤ) (hij : ¬ (up ℤ).Rel i j) :
    Total.Filtration.differential K axis i j = 0 := sorry

/-- Consecutive axis-filtered differentials compose to zero. -/
theorem Total.Filtration.differential_comp
    (axis : ℤ × ℤ →o ℤ)
    (i j k : ℤ) (hij : (up ℤ).Rel i j) (hjk : (up ℤ).Rel j k) :
    Total.Filtration.differential K axis i j ≫ Total.Filtration.differential K axis j k = 0 := sorry

/-- The filtered complex obtained from an increasing axis on a total complex. -/
@[stacks 0130 "axis-filtered total complex"]
noncomputable def Total.Filtration.total
    (axis : ℤ × ℤ →o ℤ) :
    FilteredComplex C where
  X := Total.Filtration.object K axis
  d := Total.Filtration.differential K axis
  shape := Total.Filtration.differential_shape K axis
  d_comp_d' := Total.Filtration.differential_comp K axis

/-- Forgetting an axis filtration recovers the underlying total complex. -/
@[simp]
theorem Total.Filtration.total_underlying
    (axis : ℤ × ℤ →o ℤ) :
    (Total.Filtration.total K axis).underlying = K.total (up ℤ) := sorry

end AxisComplex

/-- The endomorphism of total degree `n` that retains exactly the summands whose horizontal
degree is at least `p`. -/
noncomputable abbrev First.Filtration.cutoff (n p : ℤ) :
    (K.total (up ℤ)).X n ⟶ (K.total (up ℤ)).X n :=
  Total.Filtration.cutoff K OrderHom.fst n p

/-- The endomorphism of total degree `n` that retains exactly the summands whose vertical degree
is at least `p`. -/
noncomputable abbrev Second.Filtration.cutoff (n p : ℤ) :
    (K.total (up ℤ)).X n ⟶ (K.total (up ℤ)).X n :=
  Total.Filtration.cutoff K OrderHom.snd n p

/-- The first cutoff endomorphism is the identity on a retained total-complex summand and zero on
a discarded summand. -/
@[stacks 0130 "first filtration cutoff on total-complex summands", reassoc (attr := simp)]
theorem First.Filtration.ι_cutoff (n p i j : ℤ)
    (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = n) :
    K.ιTotal (up ℤ) i j n h ≫ (First.Filtration.cutoff K) n p =
      if p ≤ i then K.ιTotal (up ℤ) i j n h else 0 := sorry

/-- The second cutoff endomorphism is the identity on a retained total-complex summand and zero on
a discarded summand. -/
@[stacks 0130 "second filtration cutoff on total-complex summands", reassoc (attr := simp)]
theorem Second.Filtration.ι_cutoff (n p i j : ℤ)
    (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (i, j) = n) :
    K.ιTotal (up ℤ) i j n h ≫ (Second.Filtration.cutoff K) n p =
      if p ≤ j then K.ιTotal (up ℤ) i j n h else 0 := sorry

section HasImages

variable [HasImages C]

/-- The `p`-th stage of the first filtration on total degree `n`, obtained by retaining horizontal
indices at least `p`. -/
noncomputable abbrev First.Filtration.stage
    (n p : ℤ) :
    Subobject ((K.total (up ℤ)).X n) :=
  Total.Filtration.stage K OrderHom.fst n p

/-- The `p`-th stage of the second filtration on total degree `n`, obtained by retaining vertical
indices at least `p`. -/
noncomputable abbrev Second.Filtration.stage
    (n p : ℤ) :
    Subobject ((K.total (up ℤ)).X n) :=
  Total.Filtration.stage K OrderHom.snd n p

/-- Increasing the horizontal cutoff decreases the first filtration stage. -/
theorem First.Filtration.stage_antitone
    (n : ℤ) :
    Antitone ((First.Filtration.stage K) n) := sorry

/-- Increasing the vertical cutoff decreases the second filtration stage. -/
theorem Second.Filtration.stage_antitone
    (n : ℤ) :
    Antitone ((Second.Filtration.stage K) n) := sorry

/-- The first filtration stages form a monotone family when indexed by `ℤᵒᵈ`. -/
theorem First.Filtration.stage_monotone
    (n : ℤ) :
    Monotone (fun p : ℤᵒᵈ ↦ (First.Filtration.stage K) n (OrderDual.ofDual p)) := sorry

/-- The second filtration stages form a monotone family when indexed by `ℤᵒᵈ`. -/
theorem Second.Filtration.stage_monotone
    (n : ℤ) :
    Monotone (fun p : ℤᵒᵈ ↦ (Second.Filtration.stage K) n (OrderDual.ofDual p)) := sorry

/-- Total degree `n` equipped with the first, horizontal-tail filtration. -/
@[stacks 0130 "first axis-filtered total object"]
noncomputable abbrev First.Filtration.object (n : ℤ) : FilteredObject C :=
  Total.Filtration.object K OrderHom.fst n

/-- Total degree `n` equipped with the second, vertical-tail filtration. -/
@[stacks 0130 "second axis-filtered total object"]
noncomputable abbrev Second.Filtration.object (n : ℤ) : FilteredObject C :=
  Total.Filtration.object K OrderHom.snd n

/-- The total differential preserves the first filtration. -/
theorem First.Filtration.differential_preserves
    (i j : ℤ) :
    ∀ p : ℤ,
      (((First.Filtration.object K) j).filtration.stage p).Factors
        ((((First.Filtration.object K) i).filtration.stage p).arrow ≫
          (K.total (up ℤ)).d i j) := sorry

/-- The total differential preserves the second filtration. -/
theorem Second.Filtration.differential_preserves
    (i j : ℤ) :
    ∀ p : ℤ,
      (((Second.Filtration.object K) j).filtration.stage p).Factors
        ((((Second.Filtration.object K) i).filtration.stage p).arrow ≫
          (K.total (up ℤ)).d i j) := sorry

/-- The total differential as a morphism between first-filtered total degrees. -/
@[stacks 0130 "first axis-filtered total differential"]
noncomputable abbrev First.Filtration.differential
    (i j : ℤ) : (First.Filtration.object K) i ⟶ (First.Filtration.object K) j :=
  Total.Filtration.differential K OrderHom.fst i j

/-- The total differential as a morphism between second-filtered total degrees. -/
@[stacks 0130 "second axis-filtered total differential"]
noncomputable abbrev Second.Filtration.differential
    (i j : ℤ) : (Second.Filtration.object K) i ⟶ (Second.Filtration.object K) j :=
  Total.Filtration.differential K OrderHom.snd i j

/-- The first-filtered total differential vanishes away from the cochain-complex shape. -/
theorem First.Filtration.differential_shape
    (i j : ℤ) (hij : ¬ (up ℤ).Rel i j) : (First.Filtration.differential K) i j = 0 := sorry

/-- The second-filtered total differential vanishes away from the cochain-complex shape. -/
theorem Second.Filtration.differential_shape
    (i j : ℤ) (hij : ¬ (up ℤ).Rel i j) : (Second.Filtration.differential K) i j = 0 := sorry

/-- Consecutive first-filtered total differentials compose to zero. -/
theorem First.Filtration.differential_comp
    (i j k : ℤ) (hij : (up ℤ).Rel i j) (hjk : (up ℤ).Rel j k) :
    (First.Filtration.differential K) i j ≫ (First.Filtration.differential K) j k = 0 := sorry

/-- Consecutive second-filtered total differentials compose to zero. -/
theorem Second.Filtration.differential_comp
    (i j k : ℤ) (hij : (up ℤ).Rel i j) (hjk : (up ℤ).Rel j k) :
    (Second.Filtration.differential K) i j ≫ (Second.Filtration.differential K) j k = 0 := sorry

/-- Lemma 12.25.1 infrastructure: the total complex with its first, horizontal-tail filtration. -/
@[stacks 0130 "first filtered total complex of a double complex"]
noncomputable abbrev First.Filtration.total : FilteredComplex C :=
  Total.Filtration.total K OrderHom.fst

/-- Lemma 12.25.1 infrastructure: the total complex with its second, vertical-tail filtration. -/
@[stacks 0130 "second filtered total complex of a double complex"]
noncomputable abbrev Second.Filtration.total : FilteredComplex C :=
  Total.Filtration.total K OrderHom.snd

/-- Forgetting the first filtration recovers the total complex. -/
@[simp]
theorem First.Filtration.total_underlying :
    (First.Filtration.total K).underlying = K.total (up ℤ) := sorry

/-- Forgetting the second filtration recovers the total complex. -/
@[simp]
theorem Second.Filtration.total_underlying :
    (Second.Filtration.total K).underlying = K.total (up ℤ) := sorry

end HasImages

end FilteredTotal

section FilteredTotalMaps

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasImages C]
variable {K L M : HomologicalComplex₂ C (up ℤ) (up ℤ)}
variable [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)] [M.HasTotal (up ℤ)]

namespace Total.Filtration.Map

/-- A double-complex morphism preserves every common integer-axis stage. -/
theorem preserves (axis : ℤ × ℤ →o ℤ) (f : K ⟶ L) (n : ℤ) :
    ∀ p : ℤ,
      ((Total.Filtration.object L axis n).filtration.stage p).Factors
        (((Total.Filtration.object K axis n).filtration.stage p).arrow ≫
          (total.map f (up ℤ)).f n) := sorry

/-- The degree-`n` component of the total map as a morphism of axis-filtered objects. -/
noncomputable def component (axis : ℤ × ℤ →o ℤ) (f : K ⟶ L) (n : ℤ) :
    Total.Filtration.object K axis n ⟶ Total.Filtration.object L axis n where
  hom := (total.map f (up ℤ)).f n
  preserves := preserves axis f n

/-- Components of an axis-filtered total map commute with the axis-filtered differentials. -/
theorem component_comm (axis : ℤ × ℤ →o ℤ) (f : K ⟶ L) (i j : ℤ) :
    component axis f i ≫ Total.Filtration.differential L axis i j =
      Total.Filtration.differential K axis i j ≫ component axis f j := sorry

/-- A double-complex morphism induces a morphism between the corresponding axis-filtered totals. -/
@[stacks 0130 "map of axis-filtered total complexes"]
noncomputable def hom (axis : ℤ × ℤ →o ℤ) (f : K ⟶ L) :
    Total.Filtration.total K axis ⟶ Total.Filtration.total L axis where
  f := component axis f
  comm' := fun i j _ ↦ component_comm axis f i j

/-- The underlying component of an axis-filtered total map is the canonical total-map component. -/
@[simp]
theorem hom_f_hom (axis : ℤ × ℤ →o ℤ) (f : K ⟶ L) (n : ℤ) :
    ((hom axis f).f n).hom = (total.map f (up ℤ)).f n := sorry

/-- Forgetting the axis filtration from an induced map recovers the canonical total map. -/
@[simp]
theorem underlying (axis : ℤ × ℤ →o ℤ) (f : K ⟶ L) :
    FilteredComplex.underlyingMap (hom axis f) = total.map f (up ℤ) := sorry

/-- The axis-filtered total map preserves identity morphisms. -/
@[simp]
theorem id (axis : ℤ × ℤ →o ℤ) :
    hom axis (K := K) (L := K) (𝟙 K) = 𝟙 _ := sorry

/-- The axis-filtered total map preserves composition. -/
@[simp, reassoc]
theorem comp (axis : ℤ × ℤ →o ℤ) (f : K ⟶ L) (g : L ⟶ M) :
    hom axis (f ≫ g) = hom axis f ≫ hom axis g := sorry

end Total.Filtration.Map

/-- The map on total complexes induced by a double-complex morphism preserves the first
filtration.  This is the source-facing specialization of the axis-generic law. -/
theorem First.Filtration.Map.preserves (f : K ⟶ L) (n : ℤ) :
    ∀ p : ℤ,
      (((First.Filtration.object L) n).filtration.stage p).Factors
        ((((First.Filtration.object K) n).filtration.stage p).arrow ≫
          (total.map f (up ℤ)).f n) := sorry

/-- The map on total complexes induced by a double-complex morphism preserves the second
filtration.  This is the source-facing specialization of the axis-generic law. -/
theorem Second.Filtration.Map.preserves (f : K ⟶ L) (n : ℤ) :
    ∀ p : ℤ,
      (((Second.Filtration.object L) n).filtration.stage p).Factors
        ((((Second.Filtration.object K) n).filtration.stage p).arrow ≫
          (total.map f (up ℤ)).f n) := sorry

/-- The degree-`n` component of the first-filtered total map induced by a double-complex
morphism. -/
noncomputable abbrev First.Filtration.Map.component (f : K ⟶ L) (n : ℤ) :
    (First.Filtration.object K) n ⟶ (First.Filtration.object L) n :=
  Total.Filtration.Map.component OrderHom.fst f n

/-- The degree-`n` component of the second-filtered total map induced by a double-complex
morphism. -/
noncomputable abbrev Second.Filtration.Map.component (f : K ⟶ L) (n : ℤ) :
    (Second.Filtration.object K) n ⟶ (Second.Filtration.object L) n :=
  Total.Filtration.Map.component OrderHom.snd f n

/-- Components of the first-filtered total map commute with the differentials. -/
theorem First.Filtration.Map.component_comm (f : K ⟶ L) (i j : ℤ)
    :
    First.Filtration.Map.component f i ≫ (First.Filtration.differential L) i j =
      (First.Filtration.differential K) i j ≫ First.Filtration.Map.component f j := sorry

/-- Components of the second-filtered total map commute with the differentials. -/
theorem Second.Filtration.Map.component_comm (f : K ⟶ L) (i j : ℤ)
    :
    Second.Filtration.Map.component f i ≫ (Second.Filtration.differential L) i j =
      (Second.Filtration.differential K) i j ≫ Second.Filtration.Map.component f j := sorry

/-- A morphism of double complexes induces a morphism between their first-filtered total
complexes. -/
@[stacks 0130 "first filtered total map"]
noncomputable abbrev First.Filtration.Map.hom (f : K ⟶ L) :
    (First.Filtration.total K) ⟶ (First.Filtration.total L) :=
  Total.Filtration.Map.hom OrderHom.fst f

/-- A morphism of double complexes induces a morphism between their second-filtered total
complexes. -/
@[stacks 0130 "second filtered total map"]
noncomputable abbrev Second.Filtration.Map.hom (f : K ⟶ L) :
    (Second.Filtration.total K) ⟶ (Second.Filtration.total L) :=
  Total.Filtration.Map.hom OrderHom.snd f

/-- The underlying degreewise morphism of the first-filtered total map is the canonical total
map. -/
@[simp]
theorem First.Filtration.Map.hom_f_hom (f : K ⟶ L) (n : ℤ) :
    ((First.Filtration.Map.hom f).f n).hom = (total.map f (up ℤ)).f n := sorry

/-- The underlying degreewise morphism of the second-filtered total map is the canonical total
map. -/
@[simp]
theorem Second.Filtration.Map.hom_f_hom (f : K ⟶ L) (n : ℤ) :
    ((Second.Filtration.Map.hom f).f n).hom = (total.map f (up ℤ)).f n := sorry

/-- Forgetting the first filtration from the induced map recovers the canonical map on total
complexes. -/
@[simp]
theorem First.Filtration.Map.underlying (f : K ⟶ L) :
    FilteredComplex.underlyingMap (First.Filtration.Map.hom f) = total.map f (up ℤ) := sorry

/-- Forgetting the second filtration from the induced map recovers the canonical map on total
complexes. -/
@[simp]
theorem Second.Filtration.Map.underlying (f : K ⟶ L) :
    FilteredComplex.underlyingMap (Second.Filtration.Map.hom f) = total.map f (up ℤ) := sorry

/-- The first-filtered total map preserves identity morphisms. -/
@[simp]
theorem First.Filtration.Map.id :
    First.Filtration.Map.hom (K := K) (L := K) (𝟙 K) = 𝟙 _ := sorry

/-- The second-filtered total map preserves identity morphisms. -/
@[simp]
theorem Second.Filtration.Map.id :
    Second.Filtration.Map.hom (K := K) (L := K) (𝟙 K) = 𝟙 _ := sorry

/-- The first-filtered total map preserves composition. -/
@[simp, reassoc]
theorem First.Filtration.Map.comp (f : K ⟶ L) (g : L ⟶ M) :
    First.Filtration.Map.hom (f ≫ g) = First.Filtration.Map.hom f ≫ First.Filtration.Map.hom g := sorry

/-- The second-filtered total map preserves composition. -/
@[simp, reassoc]
theorem Second.Filtration.Map.comp (f : K ⟶ L) (g : L ⟶ M) :
    Second.Filtration.Map.hom (f ≫ g) = Second.Filtration.Map.hom f ≫ Second.Filtration.Map.hom g := sorry

end FilteredTotalMaps

namespace Total.Filtration

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasImages C]
variable {K : HomologicalComplex₂ C (up ℤ) (up ℤ)} [K.HasTotal (up ℤ)]

/-- Finite antidiagonal support makes every monotone-axis filtration of the total complex finite.

The axis is arbitrary, with monotonicity bundled in its `OrderHom` structure. The first and
second standard filtrations are thin specializations of this theorem.
-/
@[stacks 0132 "finite axis filtration of a double complex"]
theorem hasFiniteFiltrations
    (hfin : AntidiagonalSupport.Finite K)
    (axis : ℤ × ℤ →o ℤ) :
    (Total.Filtration.total K axis).HasFiniteFiltrations := sorry

end Total.Filtration

namespace AntidiagonalSupport.Finite

section FiniteFiltrations

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasImages C]
variable {K : HomologicalComplex₂ C (up ℤ) (up ℤ)} [K.HasTotal (up ℤ)]

/-- Finite antidiagonal support makes the first filtration finite in every total degree. -/
@[stacks 0132 "finite first filtration of a double complex"]
theorem First.hasFiniteFiltrations (hfin : AntidiagonalSupport.Finite K) :
    (First.Filtration.total K).HasFiniteFiltrations := sorry

/-- Finite antidiagonal support makes the second filtration finite in every total degree. -/
@[stacks 0132 "finite second filtration of a double complex"]
theorem Second.hasFiniteFiltrations (hfin : AntidiagonalSupport.Finite K) :
    (Second.Filtration.total K).HasFiniteFiltrations := sorry

end FiniteFiltrations

end AntidiagonalSupport.Finite

end HomologicalComplex₂
