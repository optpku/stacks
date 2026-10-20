/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.DifferentialRescale

/-!
# Explicit equivalence for unit differential rescaling

The generic unit-rescaling functor has a canonical inverse family.  This leaf packages the
inverse, unit, counit, and triangle law as a reusable categorical equivalence, so clients that
need the actual inverse data do not have to reconstruct it from `Functor.asEquivalence`.

@stack 0194
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u t

namespace CategoryTheory.HomologicalComplex.Rescale.Units

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]
variable {ι : Type t} {c : ComplexShape ι}

namespace equivalence

/-- The triangle law for the explicit inverse of unit-family rescaling. -/
@[stacks 0194 "unit-family rescaling equivalence triangle"]
theorem triangle (s : ι → (CatCenter C)ˣ) (K : HomologicalComplex C c) :
    (Units.functor (C := C) (c := c) s).map
        ((compInv.natIso (C := C) (c := c) s).symm.hom.app K) ≫
      (invComp.natIso (C := C) (c := c) s).hom.app
        ((Units.functor (C := C) (c := c) s).obj K) = 𝟙 _ := sorry

end equivalence

/-- The explicit categorical equivalence supplied by pointwise inverse unit rescaling. -/
@[stacks 0194 "unit-family rescaling categorical equivalence"]
noncomputable def equivalence (s : ι → (CatCenter C)ˣ) :
    HomologicalComplex C c ≌ HomologicalComplex C c where
  functor := Units.functor (C := C) (c := c) s
  inverse := Units.functor (C := C) (c := c) (fun i ↦ (s i)⁻¹)
  unitIso := (compInv.natIso (C := C) (c := c) s).symm
  counitIso := invComp.natIso (C := C) (c := c) s
  functor_unitIso_comp K := equivalence.triangle s K

namespace equivalence

/-- The forward functor of the explicit unit-rescaling equivalence. -/
@[simp, stacks 0194 "unit-family rescaling equivalence forward functor"]
theorem functor (s : ι → (CatCenter C)ˣ) :
    (equivalence (C := C) (c := c) s).functor =
      Units.functor (C := C) (c := c) s := sorry

/-- The inverse functor of the explicit unit-rescaling equivalence. -/
@[simp, stacks 0194 "unit-family rescaling equivalence inverse functor"]
theorem inverse (s : ι → (CatCenter C)ˣ) :
    (equivalence (C := C) (c := c) s).inverse =
      Units.functor (C := C) (c := c) (fun i ↦ (s i)⁻¹) := sorry

/-- The unit of the explicit equivalence is the inverse of the unit-then-inverse comparison. -/
@[simp, stacks 0194 "unit-family rescaling equivalence unit"]
theorem unitIso (s : ι → (CatCenter C)ˣ) :
    (equivalence (C := C) (c := c) s).unitIso =
      (compInv.natIso (C := C) (c := c) s).symm := sorry

/-- The counit of the explicit equivalence is the inverse-then-unit comparison. -/
@[simp, stacks 0194 "unit-family rescaling equivalence counit"]
theorem counitIso (s : ι → (CatCenter C)ˣ) :
    (equivalence (C := C) (c := c) s).counitIso =
      invComp.natIso (C := C) (c := c) s := sorry

end equivalence

end CategoryTheory.HomologicalComplex.Rescale.Units
