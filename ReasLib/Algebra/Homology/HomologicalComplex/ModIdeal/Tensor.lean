/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.ModIdeal
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor models for complexes modulo an ideal

This leaf records the canonical chain-level comparison between tensoring a complex by a
quotient ring and reducing the complex termwise modulo the ideal.  The derived category only
uses the resulting map as a model comparison; no flatness assertion is made here.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u w

namespace HomologicalComplex.ModIdeal

variable {A : Type u} [CommRing A]
variable {ι : Type w} {c : ComplexShape ι}

/-- Tag 00DV: the tensor-complex model of a termwise quotient complex. -/
@[stacks 00DV "tensor-complex model for an ideal quotient"]
abbrev tensorQuotientComplex (I : Ideal A)
    (K : HomologicalComplex (ModuleCat A) c) :
    HomologicalComplex (ModuleCat A) c :=
  ModuleCat.ExtendScalars.tensorComplex (S := A ⧸ I) K

/-- Tag 00DV: tensoring by `A ⧸ I` is canonically identified with reduction modulo `I`. -/
@[stacks 00DV "tensoring by a quotient ring and reducing a complex"]
noncomputable def tensorQuotientIso (I : Ideal A)
    (K : HomologicalComplex (ModuleCat A) c) :
    tensorQuotientComplex I K ≅ restrictedComplex I K :=
  (ModuleCat.ExtendScalars.restrictTensorComplexIso
      (S := A ⧸ I) K).symm ≪≫
    ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).mapHomologicalComplex c).mapIso
      (extensionIso I K)

/-- The degreewise right-tensor model `K ⊗ (A ⧸ I)` of a termwise quotient complex. -/
@[stacks 00DV "right-tensor model for an ideal quotient"]
abbrev tensorRightQuotientComplex (I : Ideal A)
    (K : HomologicalComplex (ModuleCat A) c) :
    HomologicalComplex (ModuleCat A) c :=
  ((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex c).obj K

/-- Right tensoring by `A ⧸ I` is canonically identified with reduction modulo `I`.
The comparison is the base-category braiding followed by `tensorQuotientIso`. -/
@[stacks 00DV "right tensoring by a quotient ring and reducing a complex"]
noncomputable def tensorRightQuotientIso (I : Ideal A)
    (K : HomologicalComplex (ModuleCat A) c) :
    tensorRightQuotientComplex I K ≅ restrictedComplex I K :=
  (NatIso.mapHomologicalComplex
      (BraidedCategory.tensorLeftIsoTensorRight (ModuleCat.of A (A ⧸ I))) c).symm.app K ≪≫
    tensorQuotientIso I K

/-- The degree-`i` component of `tensorQuotientIso` is the module tensor/quotient comparison. -/
@[simp, stacks 00DV "component formula for tensoring by an ideal quotient"]
theorem tensorQuotientIso_app (I : Ideal A)
    (K : HomologicalComplex (ModuleCat A) c) (i : ι) :
    HomologicalComplex.Hom.isoApp (tensorQuotientIso I K) i =
      (ModuleCat.ExtendScalars.restrictTensorIso
          (S := A ⧸ I) (K.X i)).symm ≪≫
        (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).mapIso
          (extensionTermIso I K i) := sorry

/-- The tensor/quotient comparison is natural in maps of complexes. -/
@[reassoc, stacks 00DV "naturality of the left tensor/quotient comparison"]
theorem tensorQuotientIso_hom_naturality (I : Ideal A)
    {K L : HomologicalComplex (ModuleCat A) c} (f : K ⟶ L) :
    ((tensorLeft (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex c).map f ≫
        (tensorQuotientIso I L).hom =
      (tensorQuotientIso I K).hom ≫ restrictedMap I f := sorry

/-- The right-tensor/quotient comparison is natural in maps of complexes. -/
@[reassoc, stacks 00DV "naturality of the right tensor/quotient comparison"]
theorem tensorRightQuotientIso_hom_naturality (I : Ideal A)
    {K L : HomologicalComplex (ModuleCat A) c} (f : K ⟶ L) :
    ((tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex c).map f ≫
        (tensorRightQuotientIso I L).hom =
      (tensorRightQuotientIso I K).hom ≫ restrictedMap I f := sorry

end HomologicalComplex.ModIdeal
