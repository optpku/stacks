/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatMorphism
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal
public import ReasLib.CategoryTheory.Monoidal.Closed.LaxMonoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback and internal Hom on ringed spaces

This file specializes the generic lax-monoidal pullback--internal-Hom comparison to ringed
spaces.  The comparison morphism is explicit data; its flat, finite-presentation isomorphism
criterion is the reusable ringed-space API.
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

open CategoryTheory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.PullbackInternalHom

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/-- The canonical comparison from the pullback of an internal Hom to the internal Hom of the
pullbacks on ringed spaces.  This is the specialization of
`Functor.LaxMonoidal.InternalHom.comparison` to module pullback. -/
@[stacks 0GMX "ringed-space specialization"]
noncomputable abbrev comparison (F G : Y.Modules) :
    (pullback f).obj ((ihom F).obj G) ⟶
      (ihom ((pullback f).obj F)).obj ((pullback f).obj G) :=
  Functor.LaxMonoidal.InternalHom.comparison (pullback f) F G

/-- The pullback--internal-Hom comparison is natural in its target module. -/
@[stacks 0GMX "ringed-space comparison naturality"]
theorem comparison_naturality (F : Y.Modules) {G H : Y.Modules} (g : G ⟶ H) :
    (ihom F ⋙ pullback f).map g ≫ comparison f F H =
      comparison f F G ≫
        (pullback f ⋙ ihom ((pullback f).obj F)).map g := sorry

/-- The pullback--internal-Hom comparison is contravariantly natural in its source module. -/
@[stacks 0GMX "ringed-space comparison left naturality"]
theorem comparison_naturality_left {E F : Y.Modules} (g : E ⟶ F) (G : Y.Modules) :
    comparison f F G ≫
        (MonoidalClosed.pre ((pullback f).map g)).app ((pullback f).obj G) =
      (pullback f).map ((MonoidalClosed.pre g).app G) ≫ comparison f E G := sorry

/-- For a fixed source module, the pullback--internal-Hom comparisons form a natural
transformation in the target module. -/
@[stacks 0GMX "ringed-space natural comparison"]
noncomputable abbrev natTrans (F : Y.Modules) :
    ihom F ⋙ pullback f ⟶ pullback f ⋙ ihom ((pullback f).obj F) :=
  Functor.LaxMonoidal.InternalHom.natTrans (pullback f) F

/-- A component of `natTrans` is the canonical pullback--internal-Hom comparison. -/
@[simp, stacks 0GMX "ringed-space comparison naturality component"]
theorem natTrans_app (F G : Y.Modules) :
    (natTrans f F).app G = comparison f F G := sorry

/-- Lemma 17.22.5 (0C6I): pullback along a flat morphism of ringed spaces commutes with internal
Hom from a finitely presented module. -/
@[stacks 0C6I]
theorem isIso_of_isFlat
    (F G : Y.Modules) [F.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    IsIso (comparison f F G) := sorry

/-- Flatness and finite presentation provide the canonical invertibility instance for the
pullback--internal-Hom comparison. -/
@[stacks 0C6I "flat comparison isomorphism instance", instance]
noncomputable instance comparison_isIso_of_isFlat
    (F G : Y.Modules) [F.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    IsIso (comparison f F G) := sorry

/-- The named inverse of the flat pullback--internal-Hom comparison.  Its only categorical
invertibility gate is `comparison_isIso_of_isFlat`; the generic lax-monoidal owner supplies the
underlying categorical inverse. -/
@[stacks 0C6I "flat comparison inverse"]
noncomputable abbrev comparisonInv
    (F G : Y.Modules) [F.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    (ihom ((pullback f).obj F)).obj ((pullback f).obj G) ⟶
      (pullback f).obj ((ihom F).obj G) :=
  Functor.LaxMonoidal.InternalHom.comparisonInv (pullback f) F G

/-- The flat pullback--internal-Hom comparison followed by its named inverse is the identity. -/
@[simp, stacks 0C6I "flat comparison forward-inverse law"]
theorem comparison_comp_comparisonInv
    (F G : Y.Modules) [F.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    comparison f F G ≫ comparisonInv f F G = 𝟙 _ := sorry

/-- The named inverse followed by the flat pullback--internal-Hom comparison is the identity. -/
@[simp, stacks 0C6I "flat comparison inverse-forward law"]
theorem comparisonInv_comp_comparison
    (F G : Y.Modules) [F.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    comparisonInv f F G ≫ comparison f F G = 𝟙 _ := sorry

/-- The pullback--internal-Hom comparison as an explicit isomorphism under flatness and finite
presentation. -/
@[stacks 0C6I "flat comparison isomorphism"]
noncomputable def comparisonIso
    (F G : Y.Modules) [F.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    (pullback f).obj ((ihom F).obj G) ≅
      (ihom ((pullback f).obj F)).obj ((pullback f).obj G) :=
  { hom := comparison f F G
    inv := comparisonInv f F G
    hom_inv_id := comparison_comp_comparisonInv f F G
    inv_hom_id := comparisonInv_comp_comparison f F G }

/-- The forward map of the flat pullback--internal-Hom comparison isomorphism. -/
@[simp, stacks 0C6I "flat comparison isomorphism hom"]
theorem comparisonIso_hom
    (F G : Y.Modules) [F.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    (comparisonIso f F G).hom = comparison f F G := sorry

/-- The inverse map of the flat pullback--internal-Hom comparison isomorphism is
`comparisonInv`. -/
@[simp, stacks 0C6I "flat comparison isomorphism inverse"]
theorem comparisonIso_inv
    (F G : Y.Modules) [F.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    (comparisonIso f F G).inv = comparisonInv f F G := sorry

/-- The named inverse comparison is natural in the target module. -/
@[stacks 0C6I "flat inverse comparison naturality"]
theorem comparisonInv_naturality
    (F : Y.Modules) {G H : Y.Modules} (g : G ⟶ H)
    [F.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    (pullback f ⋙ ihom ((pullback f).obj F)).map g ≫ comparisonInv f F H =
      comparisonInv f F G ≫ (ihom F ⋙ pullback f).map g := sorry

/-- For a finitely presented source, the named inverse comparisons form a natural
transformation in the target module. -/
@[stacks 0C6I "flat inverse natural comparison"]
noncomputable def natTransInv
    (F : Y.Modules) [F.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    pullback f ⋙ ihom ((pullback f).obj F) ⟶ ihom F ⋙ pullback f where
  app G := comparisonInv f F G
  naturality _ _ g := comparisonInv_naturality f F g

/-- A component of `natTransInv` is the named comparison inverse. -/
@[simp, stacks 0C6I "flat inverse natural comparison component"]
theorem natTransInv_app
    (F G : Y.Modules) [F.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    (natTransInv f F).app G = comparisonInv f F G := sorry

/-- The forward and inverse comparison natural transformations compose to the identity. -/
@[simp, stacks 0C6I "flat natural comparison forward-inverse law"]
theorem natTrans_comp_natTransInv
    (F : Y.Modules) [F.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    natTrans f F ≫ natTransInv f F = 𝟙 _ := sorry

/-- The inverse and forward comparison natural transformations compose to the identity. -/
@[simp, stacks 0C6I "flat natural comparison inverse-forward law"]
theorem natTransInv_comp_natTrans
    (F : Y.Modules) [F.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    natTransInv f F ≫ natTrans f F = 𝟙 _ := sorry

/-- The forward and inverse comparison components compose to the identity. -/
@[simp, stacks 0C6I "flat natural comparison component forward-inverse law"]
theorem natTrans_app_comp_natTransInv_app
    (F G : Y.Modules) [F.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    (natTrans f F).app G ≫ (natTransInv f F).app G = 𝟙 _ := sorry

/-- The inverse and forward comparison components compose to the identity. -/
@[simp, stacks 0C6I "flat natural comparison component inverse-forward law"]
theorem natTransInv_app_comp_natTrans_app
    (F G : Y.Modules) [F.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    (natTransInv f F).app G ≫ (natTrans f F).app G = 𝟙 _ := sorry

/-- For a finitely presented source, the flat pullback--internal-Hom comparisons form a natural
isomorphism in the target module. -/
@[stacks 0C6I "flat comparison natural isomorphism"]
noncomputable def comparisonNatIso
    (F : Y.Modules) [F.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    ihom F ⋙ pullback f ≅ pullback f ⋙ ihom ((pullback f).obj F) :=
  { hom := natTrans f F
    inv := natTransInv f F
    hom_inv_id := natTrans_comp_natTransInv f F
    inv_hom_id := natTransInv_comp_natTrans f F }

/-- Flatness and finite presentation make the whole target-variable comparison invertible. -/
@[stacks 0C6I "flat comparison natural transformation isomorphism", instance]
noncomputable instance natTrans_isIso
    (F : Y.Modules) [F.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    IsIso (natTrans f F) := sorry

/-- The forward natural transformation of `comparisonNatIso` is the canonical comparison family. -/
@[stacks 0C6I "flat comparison natural isomorphism hom", simp]
theorem comparisonNatIso_hom
    (F : Y.Modules) [F.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    (comparisonNatIso f F).hom = natTrans f F := sorry

/-- The inverse natural transformation of `comparisonNatIso` is the named inverse family. -/
@[stacks 0C6I "flat comparison natural isomorphism inverse", simp]
theorem comparisonNatIso_inv
    (F : Y.Modules) [F.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    (comparisonNatIso f F).inv = natTransInv f F := sorry

/-- A component of `comparisonNatIso` is the pointwise flat comparison isomorphism. -/
@[simp, stacks 0C6I "flat comparison natural isomorphism component"]
theorem comparisonNatIso_app
    (f : X ⟶ Y) (F G : Y.Modules)
    [F.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    (comparisonNatIso f F).app G = comparisonIso f F G := sorry

/-- The forward component of `comparisonNatIso` is the canonical comparison morphism. -/
@[simp, stacks 0C6I "flat comparison natural isomorphism hom component"]
theorem comparisonNatIso_hom_app
    (f : X ⟶ Y) (F G : Y.Modules)
    [F.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    (comparisonNatIso f F).hom.app G = comparison f F G := sorry

/-- The inverse component of `comparisonNatIso` is the named pointwise comparison inverse. -/
@[simp, stacks 0C6I "flat comparison natural isomorphism inverse component"]
theorem comparisonNatIso_inv_app
    (f : X ⟶ Y) (F G : Y.Modules)
    [F.IsFinitePresentation] [RingedSpace.Hom.IsFlat f] :
    (comparisonNatIso f F).inv.app G = comparisonInv f F G := sorry

end AlgebraicGeometry.RingedSpace.Hom.PullbackInternalHom
