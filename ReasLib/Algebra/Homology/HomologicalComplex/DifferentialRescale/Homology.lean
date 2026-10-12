/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.DifferentialRescale
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Homology of a rescaled homological complex

The gauge comparison for a compatible source-degree unit family is functorial.  Whiskering it
with the canonical homology functor gives the reusable natural comparison used by chain,
cochain, and filtered-complex clients.

@stack 0194
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u t

namespace CategoryTheory.HomologicalComplex.Rescale

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]
variable {ι : Type t} {c : ComplexShape ι}

namespace Homology

section Comparison

variable [CategoryWithHomology C]

/-- The homology comparison induced by a source-degree gauge, in a fixed degree. -/
@[stacks 0194 "source-degree rescaling homology natural comparison"]
noncomputable def natIso (s a : ι → (CatCenter C)ˣ)
    (ha : IsPotential (c := c) s a) (i : ι) :
    Units.functor (C := C) (c := c) s ⋙
        HomologicalComplex.homologyFunctor C c i ≅
      HomologicalComplex.homologyFunctor C c i :=
  Functor.isoWhiskerRight
      (Rescale.natIso (C := C) (c := c) s a ha)
      (HomologicalComplex.homologyFunctor C c i) ≪≫
    Functor.leftUnitor (HomologicalComplex.homologyFunctor C c i)

/-- The graded homology comparison induced by a source-degree gauge. -/
@[stacks 0194 "source-degree rescaling graded homology comparison"]
noncomputable def gradedNatIso (s a : ι → (CatCenter C)ˣ)
    (ha : IsPotential (c := c) s a) :
    Units.functor (C := C) (c := c) s ⋙
        HomologicalComplex.gradedHomologyFunctor C c ≅
      HomologicalComplex.gradedHomologyFunctor C c :=
  Functor.isoWhiskerRight
      (Rescale.natIso (C := C) (c := c) s a ha)
      (HomologicalComplex.gradedHomologyFunctor C c) ≪≫
    Functor.leftUnitor (HomologicalComplex.gradedHomologyFunctor C c)

/-- The object component of the source-degree rescaling homology comparison. -/
@[simp, stacks 0194 "source-degree rescaling homology comparison component"]
theorem natIso_app (s a : ι → (CatCenter C)ˣ)
    (ha : IsPotential (c := c) s a) (i : ι) (K : HomologicalComplex C c) :
    (natIso (C := C) (c := c) s a ha i).app K =
      HomologicalComplex.homologyMapIso (Rescale.iso K s a ha) i := sorry

namespace natIso

/-- The forward homology map of the source-degree rescaling comparison. -/
@[simp, stacks 0194 "source-degree rescaling homology comparison forward map"]
theorem hom_app (s a : ι → (CatCenter C)ˣ)
    (ha : IsPotential (c := c) s a) (i : ι) (K : HomologicalComplex C c) :
    ((natIso (C := C) (c := c) s a ha i).app K).hom =
      HomologicalComplex.homologyMap (Rescale.iso K s a ha).hom i := sorry

/-- The inverse homology map of the source-degree rescaling comparison. -/
@[simp, stacks 0194 "source-degree rescaling homology comparison inverse map"]
theorem inv_app (s a : ι → (CatCenter C)ˣ)
    (ha : IsPotential (c := c) s a) (i : ι) (K : HomologicalComplex C c) :
    ((natIso (C := C) (c := c) s a ha i).app K).inv =
      HomologicalComplex.homologyMap (Rescale.iso K s a ha).inv i := sorry

end natIso

namespace gradedNatIso

/-- The forward graded homology comparison in degree `i`. -/
@[simp, stacks 0194 "source-degree graded homology comparison forward component"]
theorem hom_app (s a : ι → (CatCenter C)ˣ)
    (ha : IsPotential (c := c) s a) (K : HomologicalComplex C c) (i : ι) :
    ((gradedNatIso (C := C) (c := c) s a ha).hom.app K) i =
      HomologicalComplex.homologyMap (Rescale.iso K s a ha).hom i := sorry

/-- The inverse graded homology comparison in degree `i`. -/
@[simp, stacks 0194 "source-degree graded homology comparison inverse component"]
theorem inv_app (s a : ι → (CatCenter C)ˣ)
    (ha : IsPotential (c := c) s a) (K : HomologicalComplex C c) (i : ι) :
    ((gradedNatIso (C := C) (c := c) s a ha).inv.app K) i =
      HomologicalComplex.homologyMap (Rescale.iso K s a ha).inv i := sorry

end gradedNatIso

end Comparison

end Homology

end CategoryTheory.HomologicalComplex.Rescale
