module

public import ReasLib.Algebra.Homology.CochainComplex.MappingCone.Bounded
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

@[expose] public section

/-!
# Split-monomorphic mapping-cone factorizations of cochain maps

This leaf owns the canonical factorization of a cochain map `α : K ⟶ L` through
`L ⊞ mappingCone (𝟙 K)`.  It records the explicit middle complex and maps, the
degreewise split short complex to `mappingCone α`, the deformation retract onto `L`, and the
boundedness consequences.  The construction only needs a preadditive category with binary
biproducts, so differential-graded and derived-category applications can use it directly.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex

universe v u

namespace CochainComplex

namespace SplitMonoFactorization

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {K L : CochainComplex C ℤ}

/-- The canonical middle complex `L ⊞ mappingCone (𝟙 K)` for a split-monomorphic
factorization of a cochain map out of `K`. -/
@[stacks 013N "split-monomorphic factorization object"]
abbrev obj (K L : CochainComplex C ℤ) : CochainComplex C ℤ :=
  L ⊞ mappingCone (𝟙 K)

/-- The canonical inclusion of the source into the middle complex of the split-monomorphic
mapping-cone factorization. -/
@[stacks 013N "split-monomorphic factorization inclusion"]
abbrev ι (α : K ⟶ L) : K ⟶ obj K L :=
  biprod.lift α (mappingCone.inr (𝟙 K))

/-- The canonical map from the split-monomorphic factorization object to the mapping cone of the
original cochain map. -/
@[stacks 013N "split-monomorphic factorization cone map"]
def π (α : K ⟶ L) :
    obj K L ⟶ mappingCone α :=
  biprod.desc (mappingCone.inr α)
    (-mappingCone.map (𝟙 K) α (𝟙 K) α rfl)

/-- The two maps in the split-monomorphic mapping-cone factorization compose to zero. -/
@[simp, stacks 013N]
theorem ι_comp_π (α : K ⟶ L) :
    ι α ≫ π α = 0 := sorry

/-- The canonical degreewise split short complex associated to a cochain map. -/
@[stacks 013N "split-monomorphic factorization short complex"]
abbrev shortComplex (α : K ⟶ L) : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk
    (ι α)
    (π α)
    (ι_comp_π α)

/-- The projection from the split-monomorphic factorization object onto the original target. -/
@[stacks 013N "split-monomorphic factorization projection"]
abbrev projection (K L : CochainComplex C ℤ) :
    obj K L ⟶ L :=
  biprod.fst

/-- The section of the projection from the split-monomorphic factorization object onto the
original target. -/
@[stacks 013N "split-monomorphic factorization section"]
abbrev section_ (K L : CochainComplex C ℤ) :
    L ⟶ obj K L :=
  biprod.inl

/-- The map between split-monomorphic factorization objects induced by maps of the source and
target cochain complexes. -/
@[stacks 013N "split-monomorphic factorization map"]
def map
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) :
    obj K₁ L₁ ⟶ obj K₂ L₂ :=
  biprod.map b
    (mappingCone.map (𝟙 K₁) (𝟙 K₂) a a
      ((Category.id_comp a).trans (Category.comp_id a).symm))

/-- The map of split-monomorphic factorization objects induced by identity maps is the identity. -/
@[simp, stacks 013N]
theorem map_id (K L : CochainComplex C ℤ) :
    map (𝟙 K) (𝟙 L) = 𝟙 (obj K L) := sorry

/-- Maps of split-monomorphic factorization objects respect composition in the source and target. -/
@[stacks 013N]
theorem map_comp
    {K₁ L₁ K₂ L₂ K₃ L₃ : CochainComplex C ℤ}
    (a₁ : K₁ ⟶ K₂) (b₁ : L₁ ⟶ L₂) (a₂ : K₂ ⟶ K₃) (b₂ : L₂ ⟶ L₃) :
    map (a₁ ≫ a₂) (b₁ ≫ b₂) =
      map a₁ b₁ ≫ map a₂ b₂ := sorry

/-- The factorization inclusion is natural with respect to a commuting square of cochain maps. -/
@[stacks 013N]
theorem ι_naturality
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    {α₁ : K₁ ⟶ L₁} {α₂ : K₂ ⟶ L₂}
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (h : α₁ ≫ b = a ≫ α₂) :
    ι α₁ ≫ map a b =
      a ≫ ι α₂ := sorry

/-- The map to the mapping cone is natural with respect to a commuting square of cochain maps. -/
@[stacks 013N]
theorem π_naturality
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    {α₁ : K₁ ⟶ L₁} {α₂ : K₂ ⟶ L₂}
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (h : α₁ ≫ b = a ≫ α₂) :
    map a b ≫ π α₂ =
      π α₁ ≫ mappingCone.map α₁ α₂ a b h := sorry

/-- The target projection is natural with respect to the map of factorization objects. -/
@[simp, stacks 013N]
theorem map_comp_projection
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) :
    map a b ≫ projection K₂ L₂ =
      projection K₁ L₁ ≫ b := sorry

/-- The target section is natural with respect to the map of factorization objects. -/
@[simp, stacks 013N]
theorem section_comp_map
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) :
    section_ K₁ L₁ ≫ map a b =
      b ≫ section_ K₂ L₂ := sorry

/-- The split-monomorphic factorization inclusion followed by the target projection recovers the
original cochain map. -/
@[simp, stacks 013N]
theorem ι_comp_projection (α : K ⟶ L) :
    ι α ≫
        (biprod.fst : obj K L ⟶ L) = α := sorry

/-- The canonical target section followed by the target projection is the identity. -/
@[simp, stacks 013N]
theorem section_comp_projection (K L : CochainComplex C ℤ) :
    section_ K L ≫ projection K L = 𝟙 L := sorry

/-- The target projection-section composite and the identity-cone summand add to the identity. -/
@[stacks 013N "projection-section computation"]
theorem projection_section_sum
    (K L : CochainComplex C ℤ) :
    (projection K L ≫ section_ K L) +
        ((biprod.snd : obj K L ⟶ mappingCone (𝟙 K)) ≫
          𝟙 (mappingCone (𝟙 K)) ≫
          (biprod.inr : mappingCone (𝟙 K) ⟶ obj K L)) =
      𝟙 (obj K L) := sorry

/-- Replacing the identity-cone summand by zero leaves the target projection-section composite. -/
@[stacks 013N "projection-section zero computation"]
theorem projection_section_zero
    (K L : CochainComplex C ℤ) :
    (projection K L ≫ section_ K L) +
        ((biprod.snd : obj K L ⟶ mappingCone (𝟙 K)) ≫
          (0 : mappingCone (𝟙 K) ⟶ mappingCone (𝟙 K)) ≫
          (biprod.inr : mappingCone (𝟙 K) ⟶ obj K L)) =
      projection K L ≫ section_ K L := sorry

/-- The explicit homotopy from the projection-section composite to the identity of the
split-monomorphic factorization object. -/
@[stacks 013N "split-monomorphic factorization contraction"]
noncomputable def projectionHomotopy
    (K L : CochainComplex C ℤ) :
    Homotopy
      (projection K L ≫ section_ K L)
      (𝟙 (obj K L)) :=
  let q : obj K L ⟶ mappingCone (𝟙 K) := biprod.snd
  let j : mappingCone (𝟙 K) ⟶ obj K L := biprod.inr
  let h₁ := (mappingCone.homotopyToZeroOfId K).compRight j |>.compLeft q
  let h₂ := Homotopy.add
    (Homotopy.refl (projection K L ≫ section_ K L)) h₁
  (Homotopy.ofEq (projection_section_zero K L).symm).trans
    (h₂.symm.trans (Homotopy.ofEq (projection_section_sum K L)))

/-- The canonical homotopy equivalence from the split-monomorphic factorization object to the
original target. -/
@[stacks 013N "split-monomorphic factorization homotopy equivalence"]
noncomputable def homotopyEquiv
    (K L : CochainComplex C ℤ) :
    HomotopyEquiv (obj K L) L where
  hom := projection K L
  inv := section_ K L
  homotopyHomInvId := projectionHomotopy K L
  homotopyInvHomId := Homotopy.ofEq (section_comp_projection K L)

/-- The degreewise retraction of the canonical split-monomorphic factorization inclusion. -/
@[stacks 013N]
def retraction (K L : CochainComplex C ℤ) (n : ℤ) :
    (obj K L).X n ⟶ K.X n :=
  (biprod.snd : obj K L ⟶ mappingCone (𝟙 K)).f n ≫
    (mappingCone.snd (𝟙 K)).v n n (add_zero n)

/-- The degreewise factorization inclusion followed by its canonical retraction is the identity. -/
@[simp, stacks 013N]
theorem ι_f_comp_retraction (α : K ⟶ L) (n : ℤ) :
    (ι α).f n ≫ retraction K L n = 𝟙 _ := sorry

/-- Each component of the canonical split-monomorphic factorization inclusion is split monic. -/
@[stacks 013N]
theorem ι_f_isSplitMono (α : K ⟶ L) (n : ℤ) :
    IsSplitMono ((ι α).f n) := sorry

/-- The degreewise section of the map from the factorization object to `mappingCone α`. -/
@[stacks 013N]
def coneSection (α : K ⟶ L) (n : ℤ) :
    (mappingCone α).X n ⟶ (obj K L).X n :=
  (mappingCone.snd α).v n n (add_zero n) ≫
      (biprod.inl : L ⟶ obj K L).f n -
    (mappingCone.fst α).1.v n (n + 1) rfl ≫
      (mappingCone.inl (𝟙 K)).v (n + 1) n (Int.add_neg_cancel_right n 1) ≫
        (biprod.inr : mappingCone (𝟙 K) ⟶ obj K L).f n

/-- The canonical cone section is a right inverse to the degreewise factorization-to-cone map. -/
@[simp, stacks 013N]
theorem coneSection_comp_π_f (α : K ⟶ L) (n : ℤ) :
    coneSection α n ≫ (π α).f n = 𝟙 _ := sorry

/-- The degreewise retraction and cone section decompose the identity on the factorization
object. -/
@[stacks 013N]
theorem splitting_id (α : K ⟶ L) (n : ℤ) :
    (retraction K L n ≫ (ι α).f n) +
        ((π α).f n ≫ coneSection α n) =
      𝟙 _ := sorry

/-- The canonical degreewise splitting of the split-monomorphic mapping-cone short complex. -/
@[stacks 013N "degreewise splitting of the factorization short complex"]
def splitting (α : K ⟶ L) (n : ℤ) :
    ((shortComplex α).map (eval C _ n)).Splitting where
  r := retraction K L n
  s := coneSection α n
  f_r := ι_f_comp_retraction α n
  s_g := coneSection_comp_π_f α n
  id := splitting_id α n

/-- The canonical split-monomorphic factorization object is bounded below when its source and
target are bounded below. -/
@[stacks 013N]
theorem obj_plus
    (hK : CochainComplex.plus C K) (hL : CochainComplex.plus C L) :
    CochainComplex.plus C (obj K L) := sorry

/-- The canonical split-monomorphic factorization object is bounded above when its source and
target are bounded above. -/
@[stacks 013N]
theorem obj_bounded_above
    (hK : CochainComplex.minus C K) (hL : CochainComplex.minus C L) :
    CochainComplex.minus C (obj K L) := sorry

/-- The canonical split-monomorphic factorization object is bounded when its source and target
are bounded. -/
@[stacks 013N]
theorem obj_bounded
    (hK : CochainComplex.bounded C K) (hL : CochainComplex.bounded C L) :
    CochainComplex.bounded C (obj K L) := sorry

/-- Lemma 13.9.6: the canonical split-monomorphic factorization has a contracting homotopy,
termwise split-monomorphic inclusion, and the expected projection-section computations. -/
@[stacks 013N "split-monomorphic mapping-cone factorization bridge"]
theorem factorization
    (α : K ⟶ L) :
    ∃ _ : Homotopy
        (projection K L ≫ section_ K L)
        (𝟙 (obj K L)),
      (∀ n : ℤ, IsSplitMono ((ι α).f n)) ∧
        ι α ≫
            projection K L = α ∧
        section_ K L ≫
            projection K L = 𝟙 L := sorry

end SplitMonoFactorization

end CochainComplex
