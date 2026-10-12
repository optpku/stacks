/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.Image
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Canonical boundary, cycles, and homology rows

This file packages the canonical morphism from the image of an incoming differential to
cycles.  Its defining computations exhibit the image--cycles--homology row as a short exact
sequence.  The API works for an arbitrary complex shape, so cochain-complex applications use it
directly at the consecutive indices `p` and `p + 1`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} {c : ComplexShape ι}

/-- Cycles map trivially to the image of every outgoing differential. -/
@[reassoc (attr := simp)]
theorem iCycles_factorThruImage (K : HomologicalComplex C c) (i j : ι) :
    K.iCycles i ≫ factorThruImage (K.d i j) = 0 := sorry

/-- The canonical short complex from cycles through a term to the image of a differential. -/
noncomputable def cyclesTermImage (K : HomologicalComplex C c) (i j : ι) : ShortComplex C :=
  ShortComplex.mk (K.iCycles i) (factorThruImage (K.d i j))
    (K.iCycles_factorThruImage i j)

/-- The first map in `cyclesTermImage` is the cycles inclusion. -/
@[simp]
theorem cyclesTermImage_f (K : HomologicalComplex C c) (i j : ι) :
    (K.cyclesTermImage i j).f = K.iCycles i := sorry

/-- The second map in `cyclesTermImage` is the factorization through the differential image. -/
@[simp]
theorem cyclesTermImage_g (K : HomologicalComplex C c) (i j : ι) :
    (K.cyclesTermImage i j).g = factorThruImage (K.d i j) := sorry

/-- The canonical cycles--term--differential-image row is short exact at consecutive indices. -/
theorem cyclesTermImage_shortExact (K : HomologicalComplex C c) (i j : ι)
    (hij : c.Rel i j) : (K.cyclesTermImage i j).ShortExact := sorry

/-- The canonical map from the image of an incoming differential to cycles at its target. -/
noncomputable def imageToCycles (K : HomologicalComplex C c) (i j : ι) :
    image (K.d i j) ⟶ K.cycles j :=
  (K.sc j).liftCycles (image.ι (K.d i j))
    (CategoryTheory.Limits.image_ι_comp_eq_zero (K.d_comp_d i j (c.next j)))

/-- Composing `imageToCycles` with the cycles inclusion recovers the image inclusion. -/
@[reassoc (attr := simp)]
theorem imageToCycles_iCycles (K : HomologicalComplex C c) (i j : ι) :
    K.imageToCycles i j ≫ K.iCycles j = image.ι (K.d i j) := sorry

/-- The map induced from a differential through its image agrees with `toCycles`. -/
@[reassoc (attr := simp)]
theorem factorThruImage_imageToCycles (K : HomologicalComplex C c) (i j : ι) :
    factorThruImage (K.d i j) ≫ K.imageToCycles i j = K.toCycles i j := sorry

/-- The canonical image-to-cycles map represents boundaries, hence has zero homology class. -/
@[reassoc (attr := simp)]
theorem imageToCycles_homologyπ (K : HomologicalComplex C c) (i j : ι) :
    K.imageToCycles i j ≫ K.homologyπ j = 0 := sorry

/-- The canonical image-to-cycles map is a monomorphism. -/
instance imageToCycles_mono (K : HomologicalComplex C c) (i j : ι) :
    Mono (K.imageToCycles i j) := sorry

/-- The canonical short complex from boundaries through cycles to homology. -/
noncomputable def imageCyclesHomology (K : HomologicalComplex C c) (i j : ι) : ShortComplex C :=
  ShortComplex.mk (K.imageToCycles i j) (K.homologyπ j)
    (K.imageToCycles_homologyπ i j)

/-- The first map in `imageCyclesHomology` is the canonical map from the differential image. -/
@[simp]
theorem imageCyclesHomology_f (K : HomologicalComplex C c) (i j : ι) :
    (K.imageCyclesHomology i j).f = K.imageToCycles i j := sorry

/-- The second map in `imageCyclesHomology` is the homology class projection. -/
@[simp]
theorem imageCyclesHomology_g (K : HomologicalComplex C c) (i j : ι) :
    (K.imageCyclesHomology i j).g = K.homologyπ j := sorry

/-- The canonical image--cycles--homology row is short exact at consecutive indices. -/
theorem imageCyclesHomology_shortExact (K : HomologicalComplex C c) (i j : ι)
    (hij : c.Rel i j) : (K.imageCyclesHomology i j).ShortExact := sorry

end HomologicalComplex
