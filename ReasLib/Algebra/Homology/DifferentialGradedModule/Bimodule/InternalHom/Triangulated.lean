/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Triangulated
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.Shift
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Shift.Category
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Triangulated

/-!
# Triangulated Fixed-Source Internal Hom

The explicit shift comparison for fixed-source internal Hom supplies the global shift
compatibility instance for its functor on DG homotopy categories. The generic DG-functor theorem
then provides triangulatedness without local instances at use sites.
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory
open DifferentialGradedCategory

namespace DifferentialGradedBimodule.InternalHom

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, x} R}

/-- The pointwise fixed-source internal-Hom shift isomorphism in the DG homotopy category. -/
@[stacks 09LH "pointwise internal-Hom shift isomorphism"]
def mapKShiftIsoApp (T : DifferentialGradedBimodule.{u, v, w, x} A B)
    (P : K R (DifferentialGradedModule.{u, v} B)) (k : ℤ) :
    ((DifferentialGradedModule.Shift.K.functor B k ⋙
        (DifferentialGradedBimodule.internalHomDgFunctor T).mapK).obj P) ≅
      (((DifferentialGradedBimodule.internalHomDgFunctor T).mapK ⋙
        DifferentialGradedModule.Shift.K.functor A k).obj P) :=
  (DifferentialGradedModule.toK A).mapIso
    (DifferentialGradedBimodule.internalHomShiftIso T P.obj k).symm

/-- The pointwise internal-Hom shift isomorphisms are natural on the DG homotopy category. -/
@[stacks 09LH "naturality of the pointwise internal-Hom shift isomorphism"]
theorem mapKShiftIso_naturality (T : DifferentialGradedBimodule.{u, v, w, x} A B) (k : ℤ)
    {P Q : K R (DifferentialGradedModule.{u, v} B)} (f : P ⟶ Q) :
    (DifferentialGradedModule.Shift.K.functor B k ⋙
          (DifferentialGradedBimodule.internalHomDgFunctor T).mapK).map f ≫
        (mapKShiftIsoApp T Q k).hom =
      (mapKShiftIsoApp T P k).hom ≫
        ((DifferentialGradedBimodule.internalHomDgFunctor T).mapK ⋙
          DifferentialGradedModule.Shift.K.functor A k).map f := sorry

/-- Fixed-source internal Hom commutes naturally with the explicit shifts on DG homotopy
categories. -/
@[stacks 09LH "internal-Hom shift isomorphism"]
def mapKShiftIso (T : DifferentialGradedBimodule.{u, v, w, x} A B) (k : ℤ) :
    DifferentialGradedModule.Shift.K.functor B k ⋙
        (DifferentialGradedBimodule.internalHomDgFunctor T).mapK ≅
      (DifferentialGradedBimodule.internalHomDgFunctor T).mapK ⋙
        DifferentialGradedModule.Shift.K.functor A k :=
  NatIso.ofComponents (fun P ↦ mapKShiftIsoApp T P k)
    (fun f ↦ mapKShiftIso_naturality T k f)

/-- The global internal-Hom shift isomorphism has the canonical pointwise hom component. -/
@[simp, stacks 09LH "internal-Hom shift isomorphism hom component"]
theorem mapKShiftIso_hom_app (T : DifferentialGradedBimodule.{u, v, w, x} A B)
    (P : K R (DifferentialGradedModule.{u, v} B)) (k : ℤ) :
    (mapKShiftIso T k).hom.app P = Iso.hom (mapKShiftIsoApp T P k) := sorry

/-- The global internal-Hom shift isomorphism has the canonical pointwise inverse component. -/
@[simp, stacks 09LH "internal-Hom shift isomorphism inverse component"]
theorem mapKShiftIso_inv_app (T : DifferentialGradedBimodule.{u, v, w, x} A B)
    (P : K R (DifferentialGradedModule.{u, v} B)) (k : ℤ) :
    (mapKShiftIso T k).inv.app P = Iso.inv (mapKShiftIsoApp T P k) := sorry

/-- Fixed-source internal Hom commutes with the canonical abstract shifts on DG homotopy
categories. -/
@[stacks 09LH "canonical shift comparison for fixed-source internal Hom"]
def mapKCommShiftIso (T : DifferentialGradedBimodule.{u, v, w, x} A B) (k : ℤ) :
    shiftFunctor (K R (DifferentialGradedModule.{u, v} B)) k ⋙
        (DifferentialGradedBimodule.internalHomDgFunctor T).mapK ≅
      (DifferentialGradedBimodule.internalHomDgFunctor T).mapK ⋙
        shiftFunctor (K R (DifferentialGradedModule.{u, v} A)) k :=
  (Functor.isoWhiskerRight
      (eqToIso (DifferentialGradedModule.Shift.K.shiftFunctor_eq B k))
      ((DifferentialGradedBimodule.internalHomDgFunctor T).mapK)).trans
    ((mapKShiftIso T k).trans
      (Functor.isoWhiskerLeft
        ((DifferentialGradedBimodule.internalHomDgFunctor T).mapK)
        (eqToIso (DifferentialGradedModule.Shift.K.shiftFunctor_eq A k).symm)))

/-- The canonical internal-Hom shift comparison agrees with the zero-shift comparison. -/
theorem mapKCommShiftIso_zero (T : DifferentialGradedBimodule.{u, v, w, x} A B) :
    mapKCommShiftIso T 0 = Functor.CommShift.isoZero
      (DifferentialGradedBimodule.internalHomDgFunctor T).mapK ℤ := sorry

/-- The canonical internal-Hom shift comparison is compatible with addition of shifts. -/
theorem mapKCommShiftIso_add (T : DifferentialGradedBimodule.{u, v, w, x} A B) (i j : ℤ) :
    mapKCommShiftIso T (i + j) = Functor.CommShift.isoAdd
      (mapKCommShiftIso T i) (mapKCommShiftIso T j) := sorry

/-- Lemma 22.31.1 (09LH): the homotopy functor induced by fixed-source internal Hom has a
canonical global shift-compatibility instance. -/
@[stacks 09LH "fixed-source internal Hom is triangulated on homotopy categories"]
noncomputable instance mapKCommShift (T : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (DifferentialGradedBimodule.internalHomDgFunctor T).mapK.CommShift ℤ where
  commShiftIso := mapKCommShiftIso T
  commShiftIso_zero := mapKCommShiftIso_zero T
  commShiftIso_add := mapKCommShiftIso_add T

/-- Lemma 22.31.1 (09LH): fixed-source internal Hom induces a triangulated functor on DG
homotopy categories. This concrete instance does not rely on a blanket exactness claim for all
DG functors. -/
@[stacks 09LH "fixed-source internal Hom is triangulated on homotopy categories"]
noncomputable instance mapK_isTriangulated
    (T : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (DifferentialGradedBimodule.internalHomDgFunctor T).mapK.IsTriangulated := sorry

section

variable (T : DifferentialGradedBimodule.{u, v, w, x} A B)

#synth (DifferentialGradedBimodule.internalHomDgFunctor T).mapK.CommShift ℤ
#synth (DifferentialGradedBimodule.internalHomDgFunctor T).mapK.IsTriangulated

end

end DifferentialGradedBimodule.InternalHom
