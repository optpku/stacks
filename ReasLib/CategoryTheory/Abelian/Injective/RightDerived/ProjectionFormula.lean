/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula.Dualizable
public import ReasLib.CategoryTheory.Monoidal.Flat
public import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection formulas for ordinary right derived functors

The canonical projection-formula mate may be right-derived after comparing derivation with
exact tensor functors on both sides.  This file owns that categorical construction; geometric
libraries only need to supply flatness, preservation of injectives, and dualizability.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction.RightDerived

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable [MonoidalCategory C] [BraidedCategory C]
variable [MonoidalCategory D] [BraidedCategory D]
variable [MonoidalPreadditive C] [MonoidalPreadditive D]
variable {L : Functor C D} {R : Functor D C} [L.Monoidal] [R.Additive]
variable [HasInjectiveResolutions D]

/-- The canonical degreewise right-derived projection-formula transformation.  Its three
factors compare right derivation with exact tensoring on the target, derive the underived
projection-formula mate, and compare right derivation with exact tensoring on the source. -/
@[stacks 01E8 "categorical right-derived mate"]
noncomputable def projectionFormulaNatTrans
    (adj : L ⊣ R) (X : C) [IsFlat X] [IsFlat (L.obj X)]
    [(tensorLeft (L.obj X)).PreservesInjectiveObjects] (q : ℕ) :
    R.rightDerived q ⋙ tensorLeft X ⟶
      tensorLeft (L.obj X) ⋙ R.rightDerived q :=
  (Functor.RightDerived.postcompExactIso R (IsFlat.exactTensorLeft X) q).inv ≫
    NatTrans.rightDerived (adj.projectionFormulaMateNatTrans X) q ≫
    (Functor.RightDerived.precompExactIso
      (IsFlat.exactTensorLeft (L.obj X)) R q).hom

/-- The degreewise right-derived projection-formula transformation is invertible when its
target-side tensor factor is right-dualizable. -/
theorem isIso_projectionFormulaNatTrans
    (adj : L ⊣ R) {X : C} (hX : IsRightDualizable X)
    [IsFlat X] [IsFlat (L.obj X)]
    [(tensorLeft (L.obj X)).PreservesInjectiveObjects] (q : ℕ) :
    IsIso (projectionFormulaNatTrans adj X q) := sorry

/-- Right derivation of an explicit underived projection-formula isomorphism.  Taking the
underived isomorphism as data keeps the inverse independent of any proof that the canonical mate
is invertible. -/
@[stacks 01E8 "categorical right-derived natural isomorphism"]
noncomputable abbrev projectionFormulaNatIsoOf
    {X : C}
    [IsFlat X] [IsFlat (L.obj X)]
    [(tensorLeft (L.obj X)).PreservesInjectiveObjects]
    (e : R ⋙ tensorLeft X ≅ tensorLeft (L.obj X) ⋙ R) (q : ℕ) :
    R.rightDerived q ⋙ tensorLeft X ≅
      tensorLeft (L.obj X) ⋙ R.rightDerived q :=
  Functor.RightDerived.exactSquareIso R
    (IsFlat.exactTensorLeft X) (IsFlat.exactTensorLeft (L.obj X)) e q

/-- If the forward map of the underived isomorphism is the canonical projection-formula mate,
then the forward map after right derivation is the canonical derived mate. -/
@[simp]
theorem projectionFormulaNatIsoOf_hom
    (adj : L ⊣ R) {X : C}
    [IsFlat X] [IsFlat (L.obj X)]
    [(tensorLeft (L.obj X)).PreservesInjectiveObjects]
    (e : R ⋙ tensorLeft X ≅ tensorLeft (L.obj X) ⋙ R)
    (he : e.hom = adj.projectionFormulaMateNatTrans X) (q : ℕ) :
    (projectionFormulaNatIsoOf e q).hom = projectionFormulaNatTrans adj X q := sorry

/-- The degreewise right-derived projection-formula isomorphism associated to explicit
right-duality data.  Both the underived inverse and its derived image are constructed from data;
no `IsIso` proof is used to select an inverse. -/
@[stacks 01E8 "categorical right-derived exact-pairing isomorphism"]
noncomputable def projectionFormulaNatIso
    (adj : L ⊣ R) {X X' : C} (p : ExactPairing X X')
    [IsFlat X] [IsFlat (L.obj X)]
    [(tensorLeft (L.obj X)).PreservesInjectiveObjects] (q : ℕ) :
    R.rightDerived q ⋙ tensorLeft X ≅
      tensorLeft (L.obj X) ⋙ R.rightDerived q :=
  projectionFormulaNatIsoOf (p.projectionFormulaNatIso adj) q

/-- The forward map of the exact-pairing right-derived isomorphism is the canonical derived
projection-formula mate. -/
@[simp]
theorem projectionFormulaNatIso_hom
    (adj : L ⊣ R) {X X' : C} (p : ExactPairing X X')
    [IsFlat X] [IsFlat (L.obj X)]
    [(tensorLeft (L.obj X)).PreservesInjectiveObjects] (q : ℕ) :
    (projectionFormulaNatIso adj p q).hom =
      projectionFormulaNatTrans adj X q := sorry

end CategoryTheory.Adjunction.RightDerived

namespace CategoryTheory.IsRightDualizable.RightDerived

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable [MonoidalCategory C] [BraidedCategory C]
variable [MonoidalCategory D] [BraidedCategory D]
variable [MonoidalPreadditive C] [MonoidalPreadditive D]
variable {L : Functor C D} {R : Functor D C} [L.Monoidal] [R.Additive]
variable [HasInjectiveResolutions D]

/-- The right-derived projection-formula isomorphism obtained from a right-dualizable object.
The only choice is the standard extraction of explicit duality data from `Nonempty HasRightDual`. -/
@[stacks 01E8 "categorical right-dualizable derived isomorphism"]
noncomputable def projectionFormulaNatIso
    {X : C} (hX : IsRightDualizable X) (adj : L ⊣ R)
    [IsFlat X] [IsFlat (L.obj X)]
    [(tensorLeft (L.obj X)).PreservesInjectiveObjects] (q : ℕ) :
    R.rightDerived q ⋙ tensorLeft X ≅
      tensorLeft (L.obj X) ⋙ R.rightDerived q :=
  Adjunction.RightDerived.projectionFormulaNatIso adj
    (Classical.choice hX).exact q

/-- The forward map of the chosen-dual right-derived isomorphism is the canonical derived mate. -/
@[simp]
theorem projectionFormulaNatIso_hom
    {X : C} (hX : IsRightDualizable X) (adj : L ⊣ R)
    [IsFlat X] [IsFlat (L.obj X)]
    [(tensorLeft (L.obj X)).PreservesInjectiveObjects] (q : ℕ) :
    (projectionFormulaNatIso hX adj q).hom =
      Adjunction.RightDerived.projectionFormulaNatTrans adj X q := sorry

end CategoryTheory.IsRightDualizable.RightDerived
