/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.SmallCharts
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Global graph gluing from a fixed small Rees family

The overlap is the schematic closure of the common complement of the divisor
inside the fiber product, NOT the whole fiber product of the two blowups.
Its projections and symmetry are fixed constructions. The only unproved
assertions below are named laws about these specified maps; there is no
existential selection of W, b, charts, transition maps, or an IsResult input.

The open-projection and self-projection laws are the substantive local
good-triple comparison theorem in flat.tex, lemma-complex-and-divisor-blowup-pre.
The remaining proof debts must not be confused with completed formal proofs.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.PerfectGraphAtlas

variable {X Y : Scheme.{u}} (E : RingedSpace.ModuleDerived X.toRingedSpace)
  (hE : RingedSpace.ModuleDerived.IsPerfect E) (p : Y ⟶ X) (D : Y.IdealSheafData)

abbrev chartProduct (i j : SmallChart E hE p D) : Scheme.{u} :=
  pullback (smallPieceMap E hE p D i) (smallPieceMap E hE p D j)

/-- The common open above the complement of the original divisor. -/
def relationOpen (i j : SmallChart E hE p D) : (chartProduct E hE p D i j).Opens :=
  (pullback.fst _ _ ≫ smallPieceMap E hE p D i) ⁻¹ᵁ D.openComplement

/-- The closure ideal is the actual kernel of the specified open immersion. -/
def relationIdeal (i j : SmallChart E hE p D) :
    (chartProduct E hE p D i j).IdealSheafData :=
  (relationOpen E hE p D i j).ι.ker

/-- Schematic graph overlap, constructed by quotienting by the kernel ideal. -/
def relation (i j : SmallChart E hE p D) : Scheme.{u} :=
  (relationIdeal E hE p D i j).subscheme

def relationInclusion (i j : SmallChart E hE p D) :
    relation E hE p D i j ⟶ chartProduct E hE p D i j :=
  (relationIdeal E hE p D i j).subschemeι

instance relationInclusion_closed (i j : SmallChart E hE p D) :
    IsClosedImmersion (relationInclusion E hE p D i j) := by
  exact AlgebraicGeometry.IsClosedImmersion.instSubschemeι (relationIdeal E hE p D i j)

def relationLeft (i j : SmallChart E hE p D) :
    relation E hE p D i j ⟶ smallPiece E hE p D i :=
  relationInclusion E hE p D i j ≫ pullback.fst _ _

def relationRight (i j : SmallChart E hE p D) :
    relation E hE p D i j ⟶ smallPiece E hE p D j :=
  relationInclusion E hE p D i j ≫ pullback.snd _ _

theorem relation_over (i j : SmallChart E hE p D) :
    relationLeft E hE p D i j ≫ smallPieceMap E hE p D i =
      relationRight E hE p D i j ≫ smallPieceMap E hE p D j := by
  simp only [relationLeft, relationRight, Category.assoc, pullback.condition]

/-- Swapping the fixed fiber product preserves its off-divisor schematic
closure. This is the kernel containment for that particular symmetry, not
an existence assertion about a comparison map. -/
theorem relationSwap_kernel (i j : SmallChart E hE p D) :
    (relationInclusion E hE p D j i).ker ≤
      (relationInclusion E hE p D i j ≫
        (pullbackSymmetry (smallPieceMap E hE p D i) (smallPieceMap E hE p D j)).hom).ker := by
  sorry

/-- The comparison symmetry is the canonical quotient lift of the actual
fiber-product symmetry. Mathlib constructs this lift by quotient maps. -/
def relationSwap (i j : SmallChart E hE p D) :
    relation E hE p D i j ⟶ relation E hE p D j i :=
  IsClosedImmersion.lift (relationInclusion E hE p D j i)
    (relationInclusion E hE p D i j ≫
      (pullbackSymmetry (smallPieceMap E hE p D i) (smallPieceMap E hE p D j)).hom)
    (relationSwap_kernel E hE p D i j)

@[reassoc (attr := simp)]
theorem relationSwap_inclusion (i j : SmallChart E hE p D) :
    relationSwap E hE p D i j ≫ relationInclusion E hE p D j i =
      relationInclusion E hE p D i j ≫
        (pullbackSymmetry (smallPieceMap E hE p D i) (smallPieceMap E hE p D j)).hom :=
  IsClosedImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
theorem relationSwap_left (i j : SmallChart E hE p D) :
    relationSwap E hE p D i j ≫ relationLeft E hE p D j i =
      relationRight E hE p D i j := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ pullback.fst (smallPieceMap E hE p D j)
      (smallPieceMap E hE p D i)) (relationSwap_inclusion E hE p D i j)).trans
      ((Category.assoc _ _ _).trans (congrArg
        (fun f => relationInclusion E hE p D i j ≫ f)
        (pullbackSymmetry_hom_comp_fst (smallPieceMap E hE p D i) (smallPieceMap E hE p D j)))))

@[reassoc (attr := simp)]
theorem relationSwap_right (i j : SmallChart E hE p D) :
    relationSwap E hE p D i j ≫ relationRight E hE p D j i =
      relationLeft E hE p D i j := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ pullback.snd (smallPieceMap E hE p D j)
      (smallPieceMap E hE p D i)) (relationSwap_inclusion E hE p D i j)).trans
      ((Category.assoc _ _ _).trans (congrArg
        (fun f => relationInclusion E hE p D i j ≫ f)
        (pullbackSymmetry_hom_comp_snd (smallPieceMap E hE p D i) (smallPieceMap E hE p D j)))))

theorem relationSwap_involutive (i j : SmallChart E hE p D) :
    relationSwap E hE p D i j ≫ relationSwap E hE p D j i = 𝟙 _ := by
  apply (cancel_mono (relationInclusion E hE p D i j)).mp
  have hsym :
      (pullbackSymmetry (smallPieceMap E hE p D i) (smallPieceMap E hE p D j)).hom ≫
      (pullbackSymmetry (smallPieceMap E hE p D j) (smallPieceMap E hE p D i)).hom = 𝟙 _ :=
    (pullbackSymmetry (smallPieceMap E hE p D i) (smallPieceMap E hE p D j)).hom_inv_id
  simp only [Category.assoc, relationSwap_inclusion, relationSwap_inclusion_assoc,
    hsym, Category.comp_id, Category.id_comp]

variable [IsEffectiveCartierDivisor D.subschemeι]

/-- Both product-ideal Rees pieces have the source's local good-triple
universal property. Their off-divisor graph closure is the graph of its
unique comparison, so this fixed projection identifies an open subscheme. -/
theorem relationLeft_open (i j : SmallChart E hE p D) :
    IsOpenImmersion (relationLeft E hE p D i j) := by
  sorry

attribute [instance] relationLeft_open

/-- On a self-overlap, the graph closure is the diagonal: the Rees map is
separated and its Cartier complement is schematically dense. -/
theorem relationLeft_self_iso (i : SmallChart E hE p D) :
    IsIso (relationLeft E hE p D i i) := by
  sorry

/-- The two projections coincide on that fixed diagonal closure. -/
theorem relation_self_projections (i : SmallChart E hE p D) :
    relationLeft E hE p D i i = relationRight E hE p D i i := by
  sorry

theorem relationSwap_self (i : SmallChart E hE p D) :
    relationSwap E hE p D i i = 𝟙 _ := by
  apply (cancel_mono (relationLeft E hE p D i i)).mp
  simpa only [relationSwap_left, Category.id_comp] using
    (relation_self_projections E hE p D i).symm

abbrev tripleOverlap (i j k : SmallChart E hE p D) : Scheme.{u} :=
  pullback (relationLeft E hE p D i j) (relationLeft E hE p D i k)

/-- The prescribed projection of a triple overlap into its middle chart. -/
def tripleToMiddle (i j k : SmallChart E hE p D) :
    tripleOverlap E hE p D i j k ⟶ smallPiece E hE p D j :=
  pullback.fst _ _ ≫ relationRight E hE p D i j

/-- The fixed common-point map has image in the next overlap. This follows
from the open-projection image being the inverse image of the other base
chart; it neither supplies an arbitrary map nor chooses an overlap object. -/
theorem tripleToMiddle_range (i j k : SmallChart E hE p D) :
    Set.range (tripleToMiddle E hE p D i j k) ⊆
      Set.range (relationLeft E hE p D j k) := by
  sorry

/-- Canonical restriction of the fixed middle-chart projection. -/
def tripleToNext (i j k : SmallChart E hE p D) :
    tripleOverlap E hE p D i j k ⟶ relation E hE p D j k :=
  IsOpenImmersion.lift (relationLeft E hE p D j k)
    (tripleToMiddle E hE p D i j k) (tripleToMiddle_range E hE p D i j k)

@[reassoc (attr := simp)]
theorem tripleToNext_left (i j k : SmallChart E hE p D) :
    tripleToNext E hE p D i j k ≫ relationLeft E hE p D j k =
      tripleToMiddle E hE p D i j k := IsOpenImmersion.lift_fac _ _ _

/-- Actual map of the two pullback factors in the triple overlap. -/
def tripleTransition (i j k : SmallChart E hE p D) :
    tripleOverlap E hE p D i j k ⟶ tripleOverlap E hE p D j k i :=
  pullback.lift (tripleToNext E hE p D i j k)
    (pullback.fst _ _ ≫ relationSwap E hE p D i j)
    (by simp [tripleToMiddle])

@[reassoc (attr := simp)]
theorem tripleTransition_snd (i j k : SmallChart E hE p D) :
    tripleTransition E hE p D i j k ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ relationSwap E hE p D i j := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem tripleTransition_fst_left (i j k : SmallChart E hE p D) :
    tripleTransition E hE p D i j k ≫ pullback.fst _ _ ≫ relationLeft E hE p D j k =
      pullback.fst _ _ ≫ relationRight E hE p D i j := by
  change (pullback.lift _ _ _) ≫ _ ≫ _ = _
  rw [← Category.assoc, pullback.lift_fst, tripleToNext_left]
  rfl

/-- The three canonical overlap maps return each point and section to the
same chart. Its proof uses uniqueness of the specified local comparisons. -/
theorem tripleTransition_cocycle (i j k : SmallChart E hE p D) :
    tripleTransition E hE p D i j k ≫ tripleTransition E hE p D j k i ≫
      tripleTransition E hE p D k i j = 𝟙 _ := by
  sorry

/-- Gluing data entirely constructed from original inputs, with a small index. -/
def globalGlueData : Scheme.GlueData.{u} where
  J := SmallChart E hE p D
  U := smallPiece E hE p D
  V ij := relation E hE p D ij.1 ij.2
  f := relationLeft E hE p D
  f_id := relationLeft_self_iso E hE p D
  t := relationSwap E hE p D
  t_id := relationSwap_self E hE p D
  t' := tripleTransition E hE p D
  t_fac := tripleTransition_snd E hE p D
  cocycle := tripleTransition_cocycle E hE p D
  f_open := relationLeft_open E hE p D

/-- The global graph scheme is the actual Mathlib gluing of this Rees family. -/
def globalW : Scheme.{u} := (globalGlueData E hE p D).glued

/-- The structural morphism is the colimit of the prescribed Rees projections. -/
def globalB : globalW E hE p D ⟶ Y := by
  fapply Multicoequalizer.desc
  · exact smallPieceMap E hE p D
  rintro ⟨i, j⟩
  change relationLeft E hE p D i j ≫ smallPieceMap E hE p D i =
    (relationSwap E hE p D i j ≫ relationLeft E hE p D j i) ≫ smallPieceMap E hE p D j
  rw [relationSwap_left, relation_over]

def globalInclusion (i : SmallChart E hE p D) : smallPiece E hE p D i ⟶ globalW E hE p D :=
  (globalGlueData E hE p D).ι i

/-- On every coordinate chart, the global map is precisely its original Rees projection. -/
theorem globalInclusion_b (i : SmallChart E hE p D) :
    globalInclusion E hE p D i ≫ globalB E hE p D = smallPieceMap E hE p D i :=
  Multicoequalizer.π_desc _ _ _ _ _

def globalToOriginal : globalW E hE p D ⟶ X := globalB E hE p D ≫ p

theorem globalInclusion_toOriginal (i : SmallChart E hE p D) :
    globalInclusion E hE p D i ≫ globalToOriginal E hE p D =
      i.toChart.graphHom ≫ p := by
  rw [globalToOriginal, ← Category.assoc, globalInclusion_b]
  rfl

/-- The open chart maps of the glued scheme, supplied by the actual gluing construction. -/
def globalOpenCover : (globalW E hE p D).OpenCover :=
  (globalGlueData E hE p D).openCover

theorem globalOpenCover_map (i : SmallChart E hE p D) :
    (globalOpenCover E hE p D).f i = globalInclusion E hE p D i := rfl

theorem globalInclusions_cover (w : globalW E hE p D) :
    ∃ (i : SmallChart E hE p D) (z : smallPiece E hE p D i),
      globalInclusion E hE p D i z = w :=
  (globalGlueData E hE p D).ι_jointly_surjective w

/-- A homogeneous generator chart of a Rees piece maps to the global scheme
by the actual Proj chart inclusion followed by the actual gluing inclusion. -/
def globalAffineInclusion (i : SmallChart E hE p D) (a : i.toChart.productIdeal) :
    i.toChart.graphAffineScheme a ⟶ globalW E hE p D :=
  i.toChart.graphAffineInclusion a ≫ globalInclusion E hE p D i

/-- The global map retains the degree-zero structural map on every generator chart. -/
theorem globalAffineInclusion_b (i : SmallChart E hE p D) (a : i.toChart.productIdeal) :
    globalAffineInclusion E hE p D i a ≫ globalB E hE p D =
      i.toChart.graphAffineHom a := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => i.toChart.graphAffineInclusion a ≫ f)
      (globalInclusion_b E hE p D i)).trans (i.toChart.graphAffineInclusion_hom a))

/-- The global restriction of b along its prescribed chart is literally the
given Rees projection over Y, with no additional output choice. -/
theorem globalB_chart_formula (i : SmallChart E hE p D) :
    globalInclusion E hE p D i ≫ globalB E hE p D =
      ReesProj.toSpec i.toChart.productIdeal ≫ i.U.2.fromSpec :=
  (globalInclusion_b E hE p D i).trans i.toChart.graphHom_eq

end AlgebraicGeometry.Scheme.PerfectGraphAtlas
