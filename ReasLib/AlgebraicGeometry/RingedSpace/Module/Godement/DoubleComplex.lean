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
    (row X).PreservesZeroMorphisms := sorry

/-- Applying the Godement resolution termwise to a cochain complex, with the Godement degree
as the first coordinate. -/
@[stacks 0FKT "Godement double complex"]
noncomputable abbrev bicomplex (X : RingedSpace.{u}) :
    CochainComplex X.Modules ℤ ⥤
      HomologicalComplex₂ X.Modules (up ℤ) (up ℤ) :=
  (row X).mapHomologicalComplex (up ℤ) ⋙
    HomologicalComplex₂.flipFunctor X.Modules (up ℤ) (up ℤ)

/-- The zeroth Godement column is the original complex after one Godement step. -/
@[stacks 0FKT "zeroth column of the Godement double complex"]
theorem bicomplex_obj_X_zero (X : RingedSpace.{u})
    (K : CochainComplex X.Modules ℤ) :
    ((bicomplex X).obj K).X 0 =
      ((step X).mapHomologicalComplex (up ℤ)).obj K := sorry

/-- The Godement direction starts in degree zero, while every column inherits the lower bound
of the input complex.  This is the support interface consumed by totalization and spectral
sequence APIs. -/
@[stacks 0FKT "lower bounds for the Godement double complex"]
theorem bicomplex_isStrictlyGE {a : ℤ} (X : RingedSpace.{u})
    (K : CochainComplex X.Modules ℤ)
    (hK : CochainComplex.IsStrictlyGE K a) :
    CochainComplex.IsStrictlyGE ((bicomplex X).obj K) 0 ∧
      (∀ p : ℤ,
        CochainComplex.IsStrictlyGE (((bicomplex X).obj K).X p) a) := sorry

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

/-- The degree-zero column map is a cocycle in the Godement direction. -/
@[stacks 0FKT "Godement double-complex coaugmentation cocycle"]
theorem coaugmentationZero_comp_d (X : RingedSpace.{u})
    (K : CochainComplex X.Modules ℤ) (q : ℤ)
    (hq : (up ℤ).Rel 0 q) :
    coaugmentationZero X K ≫ ((bicomplex X).obj K).d 0 q = 0 := sorry

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
    ((bicomplex X).obj K).HasTotal (up ℤ) := sorry

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
    CochainComplex.IsStrictlyGE (totalObj X K) a := sorry

/-- The Godement double complex of a bounded-below input has finite antidiagonal support. -/
@[stacks 0FKT "finite support of the Godement double complex"]
theorem bicomplex_finiteSupport {a : ℤ} (X : RingedSpace.{u})
    (K : CochainComplex X.Modules ℤ)
    (hK : CochainComplex.IsStrictlyGE K a) :
    HomologicalComplex₂.AntidiagonalSupport.Finite ((bicomplex X).obj K) := sorry

/-- The total map induced by a map of Godement double complexes. -/
@[stacks 0FKT "total Godement map"]
noncomputable abbrev totalMap (X : RingedSpace.{u})
    {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L) :
    totalObj X K ⟶ totalObj X L :=
  HomologicalComplex₂.total.map ((bicomplex X).map f) (up ℤ)

/-- Totalization respects identity maps in the Godement family. -/
@[stacks 0FKT "identity law for total Godement maps"]
theorem totalMap_id (X : RingedSpace.{u}) (K : CochainComplex X.Modules ℤ) :
    totalMap X (𝟙 K) = 𝟙 (totalObj X K) := sorry

/-- Totalization respects composition in the Godement family. -/
@[stacks 0FKT "composition law for total Godement maps"]
theorem totalMap_comp (X : RingedSpace.{u})
    {K L M : CochainComplex X.Modules ℤ} (f : K ⟶ L) (g : L ⟶ M) :
    totalMap X (f ≫ g) = totalMap X f ≫ totalMap X g := sorry

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

/-- Naturality of the total Godement comparison. -/
@[stacks 0FKT "naturality of the total Godement comparison"]
theorem totalAugmentationApp_naturality (X : RingedSpace.{u})
    {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L) :
    (𝟭 (CochainComplex X.Modules ℤ)).map f ≫ totalAugmentationApp X L =
      totalAugmentationApp X K ≫ (total X).map f := sorry

/-- The functorial comparison from an unbounded cochain complex to its total Godement complex. -/
@[stacks 0FKT "functorial total Godement comparison"]
noncomputable def totalAugmentation (X : RingedSpace.{u}) :
    𝟭 (CochainComplex X.Modules ℤ) ⟶ total X where
  app := totalAugmentationApp X
  naturality := fun {_ _} f => totalAugmentationApp_naturality X f

end AlgebraicGeometry.RingedSpace.Godement
