/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Godement.DoubleComplex
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flasque
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Naturality
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-below Godement replacements

The Godement double complex is defined for arbitrary cochain complexes.  This file records the
bounded-below support and flasque-term properties needed to use its total complex as a canonical
replacement.  The concrete total complex and comparison map remain the data owners; the
boundedness, flasqueness, quasi-isomorphism, and stalkwise homotopy statements are separate
property bridges.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape
open HomologicalComplex
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Godement

/-! ## The flasque term property -/

/-- The Godement namespace view of the canonical flasque module-sheaf property. -/
@[stacks 0FKT "Godement view of flasque module sheaves"]
abbrev flasque (X : RingedSpace.{u}) : ObjectProperty X.Modules :=
  Modules.flasque X

/-- Bounded-below complexes of module sheaves with flasque terms. -/
@[stacks 0FKT "bounded-below complexes with flasque terms"]
abbrev Flasque (X : RingedSpace.{u}) :=
  CochainComplex.Plus.TermsIn (flasque X)

namespace Total

variable (X : RingedSpace.{u})

/-- The underlying unbounded complex represented by a bounded-below input. -/
@[stacks 0FKT "underlying complex of a bounded-below input"]
abbrev input (F : CochainComplex.Plus X.Modules) : CochainComplex X.Modules ℤ :=
  (CochainComplex.Plus.ι X.Modules).obj F

/-! ## Boundedness and termwise flasqueness -/

/-- The total Godement complex of a bounded-below input is bounded below. -/
@[stacks 0FKT "boundedness of the total Godement complex"]
theorem plus (F : CochainComplex.Plus X.Modules) :
    CochainComplex.plus X.Modules
      ((total X).obj ((CochainComplex.Plus.ι X.Modules).obj F)) := sorry

/-- The Godement double complex of a bounded-below input has finite antidiagonal support. -/
@[stacks 0FKT "finite support of a bounded-below Godement total"]
theorem finiteSupport (F : CochainComplex.Plus X.Modules) :
    HomologicalComplex₂.AntidiagonalSupport.Finite
      ((bicomplex X).obj (input X F)) := sorry

/-- The total Godement complex of a bounded-below input has some lower bound. -/
@[stacks 0FKT "lower bound of a bounded-below Godement total"]
theorem lowerBound (F : CochainComplex.Plus X.Modules) :
    ∃ a : ℤ, CochainComplex.IsStrictlyGE (totalObj X (input X F)) a := sorry

/-- The total Godement complex of a bounded-below input is termwise in the canonical flasque
module-sheaf property. -/
@[stacks 0FKT "termwise flasque property of a bounded-below Godement total"]
theorem termwiseFlasque (F : CochainComplex.Plus X.Modules) :
    CochainComplex.termsIn (flasque X) (totalObj X (input X F)) := sorry

/-- Every term of a total Godement complex of a bounded-below input is flasque. -/
@[stacks 0FKT "flasque terms of the total Godement complex"]
theorem term_isFlasque (F : CochainComplex.Plus X.Modules) (n : ℤ) :
    flasque X (((total X).obj ((CochainComplex.Plus.ι X.Modules).obj F)).X n) := sorry

/-- The total Godement complex, bundled as a bounded-below complex. -/
@[stacks 0FKT "bounded-below total Godement complex"]
noncomputable def toPlus (F : CochainComplex.Plus X.Modules) :
    CochainComplex.Plus X.Modules :=
  ⟨(total X).obj ((CochainComplex.Plus.ι X.Modules).obj F), plus X F⟩

/-- The total Godement complex, bundled with its termwise flasque property. -/
@[stacks 0FKT "flasque bounded-below total Godement complex"]
noncomputable def toFlasque (F : CochainComplex.Plus X.Modules) :
    Flasque X :=
  ⟨toPlus X F, term_isFlasque X F⟩

/-- The bounded-below total Godement replacement functor. -/
@[stacks 0FKT "bounded-below total Godement replacement functor"]
noncomputable def replacement :
    CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules :=
  (CochainComplex.plus X.Modules).lift
    ((CochainComplex.Plus.ι X.Modules) ⋙ total X) (plus X)

/-- The functorial total Godement replacement with its termwise flasque target package. -/
@[stacks 0FKT "functorial flasque Godement replacement"]
noncomputable def flasqueReplacement :
    CochainComplex.Plus X.Modules ⥤ Flasque X :=
  ObjectProperty.lift (fun K : CochainComplex.Plus X.Modules =>
      ∀ n : ℤ, flasque X (K.obj.X n))
    (replacement X) (term_isFlasque X)

/-! ## Comparison maps -/

/-- The comparison from a bounded-below complex to its total Godement replacement. -/
@[stacks 0FKT "bounded-below Godement comparison"]
noncomputable def comparison :
    𝟭 (CochainComplex.Plus X.Modules) ⟶ replacement X :=
  (CochainComplex.plus X.Modules).liftNatTrans
    (fun F => F.property) (plus X)
    (Functor.whiskerLeft (CochainComplex.Plus.ι X.Modules) (totalAugmentation X))

/-- The bounded-below Godement comparison, viewed as a map into the bundled target. -/
@[stacks 0FKT "comparison into the bundled Godement replacement"]
noncomputable abbrev comparisonMap (F : CochainComplex.Plus X.Modules) :
    (CochainComplex.Plus.ι X.Modules).obj F ⟶
      (CochainComplex.Plus.ι X.Modules).obj ((replacement X).obj F) :=
  ((comparison X).app F).hom

/-- The ambient cochain map underlying the bounded-below Godement comparison. -/
@[stacks 0FKT "underlying bounded-below Godement comparison"]
theorem comparison_app_hom (F : CochainComplex.Plus X.Modules) :
    comparisonMap X F =
      totalAugmentationApp X ((CochainComplex.Plus.ι X.Modules).obj F) := sorry

/-- The comparison map is a quasi-isomorphism. -/
@[stacks 0FKT "quasi-isomorphism of the bounded-below Godement comparison"]
theorem comparison_quasiIso (F : CochainComplex.Plus X.Modules) :
    QuasiIso (comparisonMap X F) := sorry

/-! ## Stalkwise homotopy -/

/-- The stalk map induced by a bounded-below Godement comparison. -/
@[stacks 0FKT "stalk map of the bounded-below Godement comparison"]
noncomputable abbrev stalkComparison
    (F : CochainComplex.Plus X.Modules) (x : X) :=
  ((stalkModuleFunctor x).mapHomologicalComplex (up ℤ)).map (comparisonMap X F)

/-- Every stalk sees the bounded-below Godement comparison as a chain homotopy equivalence. -/
@[stacks 0FKT "stalkwise homotopy equivalence of the bounded-below Godement comparison"]
theorem stalkComparison_homotopyEquivalence
    (F : CochainComplex.Plus X.Modules) (x : X) :
    HomologicalComplex.homotopyEquivalences
      (ModuleCat (X.presheaf.stalk x)) (up ℤ)
      (stalkComparison X F x) := sorry

/-- The explicit totalized replacement satisfies the full source-facing properties. -/
@[stacks 0FKT "properties of the bounded-below Godement replacement"]
theorem replacement_spec (F : CochainComplex.Plus X.Modules) :
    QuasiIso (comparisonMap X F) ∧
      (∀ n : ℤ, flasque X (((replacement X).obj F).obj.X n)) ∧
      ∀ x : X,
        HomologicalComplex.homotopyEquivalences
          (ModuleCat (X.presheaf.stalk x)) (up ℤ)
          (stalkComparison X F x) := sorry

end Total

/-! ## Source-facing existence form -/

/-- Lemma 20.30.2 (0FKT): a bounded-below complex admits a bounded-below
termwise-flasque replacement which is quasi-isomorphic and stalkwise homotopy equivalent. -/
@[stacks 0FKT]
theorem exists_flasqueResolution (X : RingedSpace.{u})
    (F : CochainComplex.Plus X.Modules) :
    ∃ (G : CochainComplex.Plus X.Modules) (φ : F ⟶ G),
      QuasiIso φ.hom ∧
        (∀ n : ℤ,
          TopCat.Sheaf.IsFlasque ((moduleUnderlyingSheaf X).obj (G.obj.X n))) ∧
        ∀ x : X,
          HomologicalComplex.homotopyEquivalences
            (ModuleCat (X.presheaf.stalk x)) (up ℤ)
            (((stalkModuleFunctor x).mapHomologicalComplex (up ℤ)).map φ.hom) := sorry

end AlgebraicGeometry.RingedSpace.Godement
