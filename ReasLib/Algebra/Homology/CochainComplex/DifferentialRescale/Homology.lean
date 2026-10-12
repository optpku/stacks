/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.DifferentialRescale.Functor
public import ReasLib.Algebra.Homology.HomologicalComplex.DifferentialRescale.Homology

/-!
# Homology of a complex with rescaled differential

The canonical natural isomorphism removing a unit rescaling induces a canonical comparison on
homology, with a naturality theorem suitable for spectral-sequence page computations.

@stack 0194
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u w

namespace CategoryTheory.CochainComplex

namespace rescaleDifferential

variable {R : Type w} [Semiring R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

/-- Rescaling every differential by a unit does not change homology. -/
@[stacks 0194 "cochain specialization homology comparison"]
noncomputable def homologyIso
    (K : CochainComplex C ℤ) (ε : Rˣ) (n : ℤ) :
    (K.rescaleDifferential (ε : R)).homology n ≅ K.homology n :=
  (HomologicalComplex.Rescale.Homology.natIso (C := C) (c := ComplexShape.up ℤ)
      (unitFamily (C := C) ε) (potential (C := C) ε)
      (potential_isPotential (C := C) ε) n).app K

/-- The cochain homology comparison is the generic homology map of the gauge isomorphism. -/
@[simp, stacks 0194 "cochain specialization homology comparison bridge"]
theorem homologyIso_eq
    (K : CochainComplex C ℤ) (ε : Rˣ) (n : ℤ) :
    homologyIso K ε n = HomologicalComplex.homologyMapIso (iso K ε) n := sorry

/-- The forward component of the cochain homology comparison. -/
@[simp, stacks 0194 "cochain specialization homology comparison forward component"]
theorem homologyIso_hom
    (K : CochainComplex C ℤ) (ε : Rˣ) (n : ℤ) :
    (homologyIso K ε n).hom = HomologicalComplex.homologyMap (iso K ε).hom n := sorry

/-- The inverse component of the cochain homology comparison. -/
@[simp, stacks 0194 "cochain specialization homology comparison inverse component"]
theorem homologyIso_inv
    (K : CochainComplex C ℤ) (ε : Rˣ) (n : ℤ) :
    (homologyIso K ε n).inv = HomologicalComplex.homologyMap (iso K ε).inv n := sorry

namespace homologyIso

/-- The homology comparison for differential rescaling is natural in the cochain complex. -/
@[reassoc, stacks 0194 "cochain specialization homology comparison naturality"]
theorem hom_naturality
    {K L : CochainComplex C ℤ} (ε : Rˣ) (f : K ⟶ L) (n : ℤ) :
    HomologicalComplex.homologyMap (map (ε : R) f) n ≫
        (homologyIso L ε n).hom =
        (homologyIso K ε n).hom ≫
        HomologicalComplex.homologyMap f n := sorry

/-- The inverse homology comparison is natural in the rescaled complexes. -/
@[reassoc, stacks 0194 "cochain specialization inverse homology comparison naturality"]
theorem inv_naturality
    {K L : CochainComplex C ℤ} (ε : Rˣ) (f : K ⟶ L) (n : ℤ) :
    HomologicalComplex.homologyMap f n ≫
        (homologyIso L ε n).inv =
      (homologyIso K ε n).inv ≫
        HomologicalComplex.homologyMap (map (ε : R) f) n := sorry

end homologyIso

end rescaleDifferential

end CategoryTheory.CochainComplex
