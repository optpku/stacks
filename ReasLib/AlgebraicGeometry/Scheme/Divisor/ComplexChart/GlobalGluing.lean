/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.SmallCharts
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Global graph gluing of a small Rees family

The overlaps are the schematic closures of the common divisor complements in
fiber products of Rees pieces. Their projections, symmetries, and triple-overlap
transitions define a glued scheme with a structural morphism to the original base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.PerfectGraphAtlas

variable {X Y : Scheme.{u}} (E : RingedSpace.ModuleDerived X.toRingedSpace)
  (hE : RingedSpace.ModuleDerived.IsPerfect E) (p : Y ⟶ X) (D : Y.IdealSheafData)

/-- The fiber product over the base of two Rees chart pieces. -/
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

/-- The closed inclusion of the schematic overlap in the fiber product of its charts. -/
def relationInclusion (i j : SmallChart E hE p D) :
    relation E hE p D i j ⟶ chartProduct E hE p D i j :=
  (relationIdeal E hE p D i j).subschemeι

/-- The schematic overlap inclusion is a closed immersion. -/
theorem relationInclusion_closed (i j : SmallChart E hE p D) :
    IsClosedImmersion (relationInclusion E hE p D i j) := by
  exact AlgebraicGeometry.IsClosedImmersion.instSubschemeι (relationIdeal E hE p D i j)

/-- The projection from a schematic overlap to its first chart. -/
def relationLeft (i j : SmallChart E hE p D) :
    relation E hE p D i j ⟶ smallPiece E hE p D i :=
  relationInclusion E hE p D i j ≫ pullback.fst _ _

/-- The projection from a schematic overlap to its second chart. -/
def relationRight (i j : SmallChart E hE p D) :
    relation E hE p D i j ⟶ smallPiece E hE p D j :=
  relationInclusion E hE p D i j ≫ pullback.snd _ _

/-- The two projections of a schematic overlap agree over the base. -/
theorem relation_over (i j : SmallChart E hE p D) :
    relationLeft E hE p D i j ≫ smallPieceMap E hE p D i =
      relationRight E hE p D i j ≫ smallPieceMap E hE p D j := by
  simp only [relationLeft, relationRight, Category.assoc, pullback.condition]

/-- The fiber-product symmetry preserves the kernel ideal of the schematic overlap. -/
theorem relationSwap_kernel (i j : SmallChart E hE p D) :
    (relationInclusion E hE p D j i).ker ≤
      (relationInclusion E hE p D i j ≫
        (pullbackSymmetry (smallPieceMap E hE p D i) (smallPieceMap E hE p D j)).hom).ker := by
  sorry

/-- The overlap symmetry is the quotient lift of the fiber-product symmetry. -/
def relationSwap (i j : SmallChart E hE p D) :
    relation E hE p D i j ⟶ relation E hE p D j i :=
  @IsClosedImmersion.lift _ _ _ (relationInclusion E hE p D j i)
    (relationInclusion E hE p D i j ≫
      (pullbackSymmetry (smallPieceMap E hE p D i) (smallPieceMap E hE p D j)).hom)
    (relationInclusion_closed E hE p D j i) (relationSwap_kernel E hE p D i j)

/-- The overlap symmetry lifts the symmetry of the ambient fiber product. -/
@[reassoc (attr := simp)]
theorem relationSwap_inclusion (i j : SmallChart E hE p D) :
    relationSwap E hE p D i j ≫ relationInclusion E hE p D j i =
      relationInclusion E hE p D i j ≫
        (pullbackSymmetry (smallPieceMap E hE p D i) (smallPieceMap E hE p D j)).hom :=
  @IsClosedImmersion.lift_fac _ _ _ _ _ (relationInclusion_closed E hE p D j i) _

/-- The overlap symmetry interchanges the left and right projections. -/
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

/-- The overlap symmetry interchanges the right and left projections. -/
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

/-- Composing the overlap symmetry twice is the identity. -/
theorem relationSwap_involutive (i j : SmallChart E hE p D) :
    relationSwap E hE p D i j ≫ relationSwap E hE p D j i = 𝟙 _ := by
  apply (@cancel_mono _ _ _ _ _ (relationInclusion E hE p D i j)
    (@SurjectiveOnStalks.mono_of_injective _ _ _
      (relationInclusion_closed E hE p D i j).toSurjectiveOnStalks
      (relationInclusion_closed E hE p D i j).isClosedEmbedding.injective)).mp
  have hsym :
      (pullbackSymmetry (smallPieceMap E hE p D i) (smallPieceMap E hE p D j)).hom ≫
      (pullbackSymmetry (smallPieceMap E hE p D j) (smallPieceMap E hE p D i)).hom = 𝟙 _ :=
    (pullbackSymmetry (smallPieceMap E hE p D i) (smallPieceMap E hE p D j)).hom_inv_id
  simp only [Category.assoc, relationSwap_inclusion, relationSwap_inclusion_assoc,
    hsym, Category.comp_id, Category.id_comp]

variable [IsEffectiveCartierDivisor D.subschemeι]

/-- The left projection identifies the schematic overlap with an open subscheme. -/
theorem relationLeft_open (i j : SmallChart E hE p D) :
    IsOpenImmersion (relationLeft E hE p D i j) := by
  sorry

/-- On a self-overlap, the graph closure is the diagonal: the Rees map is
separated and its Cartier complement is schematically dense. -/
theorem relationLeft_self_iso (i : SmallChart E hE p D) :
    IsIso (relationLeft E hE p D i i) := by
  sorry

/-- The two projections coincide on that fixed diagonal closure. -/
theorem relation_self_projections (i : SmallChart E hE p D) :
    relationLeft E hE p D i i = relationRight E hE p D i i := by
  sorry

/-- The symmetry of a self-overlap is the identity. -/
theorem relationSwap_self (i : SmallChart E hE p D) :
    relationSwap E hE p D i i = 𝟙 _ := by
  apply (@cancel_mono _ _ _ _ _ (relationLeft E hE p D i i)
    (@IsOpenImmersion.mono _ _ _ (relationLeft_open E hE p D i i))).mp
  simpa only [relationSwap_left, Category.id_comp] using
    (relation_self_projections E hE p D i).symm

/-- The fiber product of two overlaps over their common first chart. -/
abbrev tripleOverlap (i j k : SmallChart E hE p D) : Scheme.{u} :=
  pullback (relationLeft E hE p D i j) (relationLeft E hE p D i k)

/-- The prescribed projection of a triple overlap into its middle chart. -/
def tripleToMiddle (i j k : SmallChart E hE p D) :
    tripleOverlap E hE p D i j k ⟶ smallPiece E hE p D j :=
  pullback.fst _ _ ≫ relationRight E hE p D i j

/-- The middle-chart projection of a triple overlap has image in the next overlap. -/
theorem tripleToMiddle_range (i j k : SmallChart E hE p D) :
    Set.range (tripleToMiddle E hE p D i j k) ⊆
      Set.range (relationLeft E hE p D j k) := by
  sorry

/-- Canonical restriction of the fixed middle-chart projection. -/
def tripleToNext (i j k : SmallChart E hE p D) :
    tripleOverlap E hE p D i j k ⟶ relation E hE p D j k :=
  @IsOpenImmersion.lift _ _ _ (relationLeft E hE p D j k)
    (tripleToMiddle E hE p D i j k) (relationLeft_open E hE p D j k)
    (tripleToMiddle_range E hE p D i j k)

/-- The restriction to the next overlap factors the middle-chart projection. -/
@[reassoc (attr := simp)]
theorem tripleToNext_left (i j k : SmallChart E hE p D) :
    tripleToNext E hE p D i j k ≫ relationLeft E hE p D j k =
      tripleToMiddle E hE p D i j k :=
  @IsOpenImmersion.lift_fac _ _ _ _ _ (relationLeft_open E hE p D j k) _

/-- Actual map of the two pullback factors in the triple overlap. -/
def tripleTransition (i j k : SmallChart E hE p D) :
    tripleOverlap E hE p D i j k ⟶ tripleOverlap E hE p D j k i :=
  pullback.lift (tripleToNext E hE p D i j k)
    (pullback.fst _ _ ≫ relationSwap E hE p D i j)
    (by simp [tripleToMiddle])

/-- The second projection of the triple transition is the first overlap symmetry. -/
@[reassoc (attr := simp)]
theorem tripleTransition_snd (i j k : SmallChart E hE p D) :
    tripleTransition E hE p D i j k ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ relationSwap E hE p D i j := pullback.lift_snd _ _ _

/-- The first projection of the triple transition maps to the middle chart. -/
@[reassoc (attr := simp)]
theorem tripleTransition_fst_left (i j k : SmallChart E hE p D) :
    tripleTransition E hE p D i j k ≫ pullback.fst _ _ ≫ relationLeft E hE p D j k =
      pullback.fst _ _ ≫ relationRight E hE p D i j := by
  change (pullback.lift _ _ _) ≫ _ ≫ _ = _
  rw [← Category.assoc, pullback.lift_fst, tripleToNext_left]
  rfl

/-- The three cyclic triple-overlap transitions compose to the identity. -/
theorem tripleTransition_cocycle (i j k : SmallChart E hE p D) :
    tripleTransition E hE p D i j k ≫ tripleTransition E hE p D j k i ≫
      tripleTransition E hE p D k i j = 𝟙 _ := by
  sorry

/-- The gluing data of Rees pieces along their schematic overlaps. -/
def globalGlueData : Scheme.GlueData.{u} where
  J := SmallChart E hE p D
  U := smallPiece E hE p D
  V ij := relation E hE p D ij.1 ij.2
  f := relationLeft E hE p D
  f_mono i j := @IsOpenImmersion.mono _ _ _ (relationLeft_open E hE p D i j)
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

/-- The canonical inclusion of a Rees chart piece in the glued graph scheme. -/
def globalInclusion (i : SmallChart E hE p D) : smallPiece E hE p D i ⟶ globalW E hE p D :=
  (globalGlueData E hE p D).ι i

/-- On every coordinate chart, the global map is precisely its original Rees projection. -/
theorem globalInclusion_b (i : SmallChart E hE p D) :
    globalInclusion E hE p D i ≫ globalB E hE p D = smallPieceMap E hE p D i :=
  Multicoequalizer.π_desc _ _ _ _ _

/-- The morphism from the glued graph scheme to the original scheme. -/
def globalToOriginal : globalW E hE p D ⟶ X := globalB E hE p D ≫ p

/-- Each chart inclusion commutes with the morphism to the original scheme. -/
theorem globalInclusion_toOriginal (i : SmallChart E hE p D) :
    globalInclusion E hE p D i ≫ globalToOriginal E hE p D =
      i.toChart.graphHom ≫ p := by
  rw [globalToOriginal, ← Category.assoc, globalInclusion_b]
  rfl

/-- The open chart maps of the glued scheme, supplied by the actual gluing construction. -/
def globalOpenCover : (globalW E hE p D).OpenCover :=
  (globalGlueData E hE p D).openCover

/-- The open cover maps are the canonical chart inclusions. -/
theorem globalOpenCover_map (i : SmallChart E hE p D) :
    (globalOpenCover E hE p D).f i = globalInclusion E hE p D i := rfl

/-- Every point of the glued graph scheme lies in a Rees chart piece. -/
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

/-- The structural morphism restricts on each chart to its Rees projection over the base. -/
theorem globalB_chart_formula (i : SmallChart E hE p D) :
    globalInclusion E hE p D i ≫ globalB E hE p D =
      ReesProj.toSpec i.toChart.productIdeal ≫ i.U.2.fromSpec :=
  (globalInclusion_b E hE p D i).trans i.toChart.graphHom_eq

end AlgebraicGeometry.Scheme.PerfectGraphAtlas
