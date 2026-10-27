/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Godement.Homotopy
public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalHomotopy
public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalSupport
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The Godement double complex

The Godement resolution may be applied termwise to an arbitrary cochain complex.  After extending
the nonnegative resolution direction by zero, this gives a double complex whose first direction is
the Godement direction and whose second direction is the original cochain direction.  This file
owns that double complex, its totalization, and the functorial comparison from the original complex.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open ComplexShape HomologicalComplex
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Godement

/-- The Godement cochain complex, extended by zero from nonnegative to integral degrees. -/
@[stacks 0FKT "integrally indexed Godement resolution"]
noncomputable abbrev row (X : RingedSpace.{u}) :
    X.Modules ⥤ CochainComplex X.Modules ℤ :=
  complex X ⋙ embeddingUpNat.extendFunctor X.Modules

/-- The integrally indexed Godement row preserves zero morphisms. -/
@[stacks 0FKT "Godement rows preserve zero morphisms"]
noncomputable instance row_preservesZeroMorphisms (X : RingedSpace.{u}) :
    (row X).PreservesZeroMorphisms := by
  have hiter (n : ℕ) :
      (CategoryTheory.Endofunctor.iterate (step X) n).PreservesZeroMorphisms := by
    induction n with
    | zero =>
        change (𝟭 X.Modules).PreservesZeroMorphisms
        infer_instance
    | succ n ih =>
        letI := ih
        change (CategoryTheory.Endofunctor.iterate (step X) n ⋙ step X).PreservesZeroMorphisms
        infer_instance
  letI : (complex X).PreservesZeroMorphisms := ⟨by
    intro M N
    apply HomologicalComplex.hom_ext
    intro n
    change (CategoryTheory.Endofunctor.iterate (step X) (n + 1)).map 0 = 0
    letI := hiter (n + 1)
    simp⟩
  change (complex X ⋙ embeddingUpNat.extendFunctor X.Modules).PreservesZeroMorphisms
  infer_instance

/-- Applying the Godement resolution termwise to a cochain complex, with the Godement degree
as the first coordinate. -/
@[stacks 0FKT "Godement double complex"]
noncomputable abbrev bicomplex (X : RingedSpace.{u}) :
    CochainComplex X.Modules ℤ ⥤
      HomologicalComplex₂ X.Modules (up ℤ) (up ℤ) :=
  (row X).mapHomologicalComplex (up ℤ) ⋙
    HomologicalComplex₂.flipFunctor X.Modules (up ℤ) (up ℤ)

set_option backward.isDefEq.respectTransparency false in
/-- The zeroth Godement column is the original complex after one Godement step. -/
@[stacks 0FKT "zeroth column of the Godement double complex"]
theorem bicomplex_obj_X_zero (X : RingedSpace.{u})
    (K : CochainComplex X.Modules ℤ) :
    ((bicomplex X).obj K).X 0 =
      ((step X).mapHomologicalComplex (up ℤ)).obj K := by
  have hr : embeddingUpNat.r 0 = some 0 := embeddingUpNat.r_eq_some rfl
  apply HomologicalComplex.ext
    (by
      funext q
      change HomologicalComplex.extend.X ((complex X).obj (K.X q))
        (embeddingUpNat.r 0) = (step X).obj (K.X q)
      rw [hr]
      rfl)
  intro i j hij
  change HomologicalComplex.extend.mapX ((complex X).map (K.d i j))
      (embeddingUpNat.r 0) ≫ _ = _ ≫ (step X).map (K.d i j)
  rw [HomologicalComplex.extend.mapX_some _ hr]
  change ((HomologicalComplex.extend.XIso ((complex X).obj (K.X i)) hr).hom ≫
      (step X).map (K.d i j) ≫
      (HomologicalComplex.extend.XIso ((complex X).obj (K.X j)) hr).inv) ≫
        (HomologicalComplex.extend.XIso ((complex X).obj (K.X j)) hr).hom =
      (HomologicalComplex.extend.XIso ((complex X).obj (K.X i)) hr).hom ≫
        (step X).map (K.d i j)
  simp only [Category.assoc,
    (HomologicalComplex.extend.XIso ((complex X).obj (K.X j)) hr).inv_hom_id]
  exact congrArg
    (fun g : (step X).obj (K.X i) ⟶ (step X).obj (K.X j) =>
      (HomologicalComplex.extend.XIso ((complex X).obj (K.X i)) hr).hom ≫ g)
    (Category.comp_id ((step X).map (K.d i j)))

/-- The Godement direction starts in degree zero, while every column inherits the lower bound
of the input complex.  This is the support interface consumed by totalization and spectral
sequence APIs. -/
@[stacks 0FKT "lower bounds for the Godement double complex"]
theorem bicomplex_isStrictlyGE {a : ℤ} (X : RingedSpace.{u})
    (K : CochainComplex X.Modules ℤ)
    (hK : CochainComplex.IsStrictlyGE K a) :
    CochainComplex.IsStrictlyGE ((bicomplex X).obj K) 0 ∧
      (∀ p : ℤ,
        CochainComplex.IsStrictlyGE (((bicomplex X).obj K).X p) a) := by
  constructor
  · rw [CochainComplex.isStrictlyGE_iff]
    intro p hp
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.hom_ext
    intro q
    exact (((complex X).obj (K.X q)).isZero_extend_X embeddingUpNat p
      (fun n h => by
        have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
        change (n : ℤ) = p at h
        omega)).eq_of_src _ _
  · intro p
    rw [CochainComplex.isStrictlyGE_iff]
    intro q hq
    change IsZero (((row X).obj (K.X q)).X p)
    exact (HomologicalComplex.eval X.Modules (up ℤ) p).map_isZero
      ((row X).map_isZero ((CochainComplex.isStrictlyGE_iff K a).mp hK q hq))

/-- The canonical identification of the zeroth Godement column with the termwise first
Godement step. -/
@[stacks 0FKT "zeroth Godement column comparison"]
noncomputable def zeroColumnIso (X : RingedSpace.{u})
    (K : CochainComplex X.Modules ℤ) :
    ((bicomplex X).obj K).X 0 ≅
      ((step X).mapHomologicalComplex (up ℤ)).obj K :=
  eqToIso (bicomplex_obj_X_zero X K)

/-- The degree-zero column map induced termwise by the Godement unit. -/
@[stacks 0FKT "Godement double-complex coaugmentation in degree zero"]
noncomputable def coaugmentationZero (X : RingedSpace.{u})
    (K : CochainComplex X.Modules ℤ) :
    K ⟶ ((bicomplex X).obj K).X 0 :=
  (NatTrans.mapHomologicalComplex (unit X) (up ℤ)).app K ≫
    (zeroColumnIso X K).inv

/-- The zeroth-column comparison is the unit followed by the inverse extension transport. -/
theorem coaugmentationZero_f (X : RingedSpace.{u})
    (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    (coaugmentationZero X K).f n =
      (unit X).app (K.X n) ≫
        (((complex X).obj (K.X n)).extendXIso embeddingUpNat (i := 0) rfl).inv := by
  simp only [coaugmentationZero, comp_f, NatTrans.mapHomologicalComplex_app_f,
    zeroColumnIso, eqToIso, eqToHom_f]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The map into the zeroth Godement column is natural in the original complex. -/
theorem coaugmentationZero_naturality (X : RingedSpace.{u})
    {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L) :
    f ≫ coaugmentationZero X L =
      coaugmentationZero X K ≫ ((bicomplex X).map f).f 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [comp_f, coaugmentationZero_f]
  change f.f n ≫ ((unit X).app (L.X n) ≫ _) =
    ((unit X).app (K.X n) ≫ _) ≫
      HomologicalComplex.extend.mapX ((complex X).map (f.f n)) (embeddingUpNat.r 0)
  have hr : embeddingUpNat.r 0 = some 0 := embeddingUpNat.r_eq_some rfl
  erw [HomologicalComplex.extend.mapX_some _ hr, Category.assoc,
    (HomologicalComplex.extend.XIso ((complex X).obj (K.X n)) hr).inv_hom_id_assoc]
  change f.f n ≫ ((unit X).app (L.X n) ≫ _) =
    (unit X).app (K.X n) ≫ (step X).map (f.f n) ≫ _
  erw [← Category.assoc, (unit X).naturality, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero column map is a cocycle in the Godement direction. -/
@[stacks 0FKT "Godement double-complex coaugmentation cocycle"]
theorem coaugmentationZero_comp_d (X : RingedSpace.{u})
    (K : CochainComplex X.Modules ℤ) (q : ℤ)
    (hq : (up ℤ).Rel 0 q) :
    coaugmentationZero X K ≫ ((bicomplex X).obj K).d 0 q = 0 := by
  change 0 + 1 = q at hq
  have hq' : q = 1 := by omega
  subst q
  apply HomologicalComplex.hom_ext
  intro n
  have hunit : (unit X).app (K.X n) ≫ ((complex X).obj (K.X n)).d 0 1 = 0 := by
    have h := ((augmentation X).app (K.X n)).comm 0 1
    rw [HomologicalComplex.single_obj_d, zero_comp] at h
    rw [augmentation_app_f_zero] at h
    exact h
  change (coaugmentationZero X K).f n ≫
    (((complex X).obj (K.X n)).extend embeddingUpNat).d 0 1 = 0
  erw [coaugmentationZero_f,
    HomologicalComplex.extend_d_eq _ embeddingUpNat (i := 0) (j := 1) rfl rfl]
  erw [Category.assoc,
    (((complex X).obj (K.X n)).extendXIso embeddingUpNat (i := 0) rfl).inv_hom_id_assoc,
    ← Category.assoc, hunit, zero_comp]

/-- The original cochain complex, placed in Godement degree zero, maps canonically to its
Godement double complex. -/
@[stacks 0FKT "Godement double-complex coaugmentation"]
noncomputable def coaugmentation (X : RingedSpace.{u})
    (K : CochainComplex X.Modules ℤ) :
    (CochainComplex.singleFunctor (CochainComplex X.Modules ℤ) 0).obj K ⟶
      (bicomplex X).obj K :=
  HomologicalComplex.mkHomFromSingle (coaugmentationZero X K)
    (coaugmentationZero_comp_d X K)

/-- The Godement double complexes in the image of `bicomplex` admit totalizations. -/
@[stacks 0FKT "totalization of the Godement double complex"]
noncomputable instance bicomplex_hasTotal (X : RingedSpace.{u})
    (K : CochainComplex X.Modules ℤ) :
    ((bicomplex X).obj K).HasTotal (up ℤ) := by
  intro n
  infer_instance

/-- The total object of the Godement double complex. -/
@[stacks 0FKT "total Godement object"]
noncomputable abbrev totalObj (X : RingedSpace.{u})
    (K : CochainComplex X.Modules ℤ) : CochainComplex X.Modules ℤ :=
  ((bicomplex X).obj K).total (up ℤ)

/-- The total Godement complex preserves a supplied lower bound. -/
@[stacks 0FKT "lower bound for the total Godement complex"]
theorem total_isStrictlyGE {a : ℤ} (X : RingedSpace.{u})
    (K : CochainComplex X.Modules ℤ)
    (hK : CochainComplex.IsStrictlyGE K a) :
    CochainComplex.IsStrictlyGE (totalObj X K) a := by
  obtain ⟨h₁, h₂⟩ := bicomplex_isStrictlyGE X K hK
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  have hz : IsZero ((((bicomplex X).obj K).X p).X q) := by
    by_cases hp : p < 0
    · exact (HomologicalComplex.eval X.Modules (up ℤ) q).map_isZero
        ((CochainComplex.isStrictlyGE_iff _ 0).mp h₁ p hp)
    · exact (CochainComplex.isStrictlyGE_iff _ a).mp (h₂ p) q (by
        change p + q = n at hpq
        omega)
  exact hz.eq_of_src _ _

/-- The Godement double complex of a bounded-below input has finite antidiagonal support. -/
@[stacks 0FKT "finite support of the Godement double complex"]
theorem bicomplex_finiteSupport {a : ℤ} (X : RingedSpace.{u})
    (K : CochainComplex X.Modules ℤ)
    (hK : CochainComplex.IsStrictlyGE K a) :
    HomologicalComplex₂.AntidiagonalSupport.Finite ((bicomplex X).obj K) := by
  obtain ⟨h₁, h₂⟩ := bicomplex_isStrictlyGE X K hK
  intro n
  apply (Set.finite_Icc (0 : ℤ) (n - a)).subset
  intro p hp
  change ¬ IsZero ((((bicomplex X).obj K).X p).X (n - p)) at hp
  constructor
  · by_contra h
    exact hp ((HomologicalComplex.eval X.Modules (up ℤ) (n - p)).map_isZero
      ((CochainComplex.isStrictlyGE_iff _ 0).mp h₁ p (by omega)))
  · by_contra h
    exact hp ((CochainComplex.isStrictlyGE_iff _ a).mp (h₂ p) (n - p) (by omega))

/-- The total map induced by a map of Godement double complexes. -/
@[stacks 0FKT "total Godement map"]
noncomputable abbrev totalMap (X : RingedSpace.{u})
    {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L) :
    totalObj X K ⟶ totalObj X L :=
  HomologicalComplex₂.total.map ((bicomplex X).map f) (up ℤ)

/-- Totalization respects identity maps in the Godement family. -/
@[stacks 0FKT "identity law for total Godement maps"]
theorem totalMap_id (X : RingedSpace.{u}) (K : CochainComplex X.Modules ℤ) :
    totalMap X (𝟙 K) = 𝟙 (totalObj X K) := by
  dsimp only [totalMap]
  rw [(bicomplex X).map_id]
  exact HomologicalComplex₂.total.map_id _ _

/-- Totalization respects composition in the Godement family. -/
@[stacks 0FKT "composition law for total Godement maps"]
theorem totalMap_comp (X : RingedSpace.{u})
    {K L M : CochainComplex X.Modules ℤ} (f : K ⟶ L) (g : L ⟶ M) :
    totalMap X (f ≫ g) = totalMap X f ≫ totalMap X g := by
  simp only [totalMap, Functor.map_comp, HomologicalComplex₂.total.map_comp]

/-- The total Godement complex functor on unbounded cochain complexes. -/
@[stacks 0FKT "total Godement complex functor"]
noncomputable def total (X : RingedSpace.{u}) :
    CochainComplex X.Modules ℤ ⥤ CochainComplex X.Modules ℤ where
  obj := totalObj X
  map := totalMap X
  map_id := totalMap_id X
  map_comp := totalMap_comp X

/-- The comparison from a cochain complex to its total Godement complex. -/
@[stacks 0FKT "total Godement comparison"]
noncomputable def totalAugmentationApp (X : RingedSpace.{u})
    (K : CochainComplex X.Modules ℤ) :
    K ⟶ (total X).obj K :=
  HomologicalComplex₂.ZeroColumn.Single.toTotal (coaugmentation X K)

set_option backward.isDefEq.respectTransparency false in
/-- The total comparison is the unit comparison followed by the zeroth-column inclusion. -/
theorem totalAugmentationApp_f (X : RingedSpace.{u})
    (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    (totalAugmentationApp X K).f n =
      (coaugmentationZero X K).f n ≫
        ((bicomplex X).obj K).ιTotal (up ℤ) 0 n n (Int.zero_add n) := by
  change (((singleObjXSelf (up ℤ) 0 K).inv ≫ (coaugmentation X K).f 0).f n) ≫ _ = _
  rw [coaugmentation, mkHomFromSingle_f, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the total Godement comparison. -/
@[stacks 0FKT "naturality of the total Godement comparison"]
theorem totalAugmentationApp_naturality (X : RingedSpace.{u})
    {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L) :
    (𝟭 (CochainComplex X.Modules ℤ)).map f ≫ totalAugmentationApp X L =
      totalAugmentationApp X K ≫ (total X).map f := by
  apply HomologicalComplex.hom_ext
  intro n
  change f.f n ≫ (totalAugmentationApp X L).f n =
    (totalAugmentationApp X K).f n ≫
      (HomologicalComplex₂.total.map ((bicomplex X).map f) (up ℤ)).f n
  let iK := ((bicomplex X).obj K).ιTotal (up ℤ) 0 n n (Int.zero_add n)
  let iL := ((bicomplex X).obj L).ιTotal (up ℤ) 0 n n (Int.zero_add n)
  have hi : iK ≫ (HomologicalComplex₂.total.map ((bicomplex X).map f) (up ℤ)).f n =
      (((bicomplex X).map f).f 0).f n ≫ iL :=
    HomologicalComplex₂.ιTotal_map (K := (bicomplex X).obj K) (L := (bicomplex X).obj L)
      (φ := (bicomplex X).map f) (c₁₂ := up ℤ) 0 n n (Int.zero_add n)
  have h := congr_hom (coaugmentationZero_naturality X f) n
  change f.f n ≫ (coaugmentationZero X L).f n =
    (coaugmentationZero X K).f n ≫ (((bicomplex X).map f).f 0).f n at h
  calc
    _ = f.f n ≫ ((coaugmentationZero X L).f n ≫ iL) :=
      congrArg (fun g => f.f n ≫ g) (totalAugmentationApp_f X L n)
    _ = (f.f n ≫ (coaugmentationZero X L).f n) ≫ iL :=
      (Category.assoc _ _ _).symm
    _ = ((coaugmentationZero X K).f n ≫ (((bicomplex X).map f).f 0).f n) ≫ iL :=
      congrArg (fun g => g ≫ iL) h
    _ = (coaugmentationZero X K).f n ≫ ((((bicomplex X).map f).f 0).f n ≫ iL) :=
      Category.assoc _ _ _
    _ = (coaugmentationZero X K).f n ≫
        (iK ≫ (HomologicalComplex₂.total.map ((bicomplex X).map f) (up ℤ)).f n) :=
      congrArg (fun g => (coaugmentationZero X K).f n ≫ g) hi.symm
    _ = ((coaugmentationZero X K).f n ≫ iK) ≫
        (HomologicalComplex₂.total.map ((bicomplex X).map f) (up ℤ)).f n :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg
      (fun g => g ≫ (HomologicalComplex₂.total.map ((bicomplex X).map f) (up ℤ)).f n)
      (totalAugmentationApp_f X K n).symm

/-- The functorial comparison from an unbounded cochain complex to its total Godement complex. -/
@[stacks 0FKT "functorial total Godement comparison"]
noncomputable def totalAugmentation (X : RingedSpace.{u}) :
    𝟭 (CochainComplex X.Modules ℤ) ⟶ total X where
  app := totalAugmentationApp X
  naturality := fun {_ _} f => totalAugmentationApp_naturality X f

end AlgebraicGeometry.RingedSpace.Godement
