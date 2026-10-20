module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Derived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived-to-underived base change for naive cotangent complexes

@stack 0FUY

The canonical cochain counit compares derived extension of scalars with termwise extension of
scalars.  For a two-term naive cotangent complex, this comparison becomes an isomorphism after
lower truncation at degree `-1`.
-/

@[expose] public section

noncomputable section

open CategoryTheory ComplexShape DerivedCategory.TStructure
open scoped DerivedTensorWithAlgebra NaiveCotangent

universe u

namespace Algebra.NaiveCotangent.DerivedBaseChange

variable {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S']
variable {ι κ : Type u}

/-- The cochain-level scalar extension used by the derived-to-underived comparison. -/
@[stacks 0FUY "cochain scalar extension"]
noncomputable abbrev scalarExtendedCochain (σ : S →+* S') :
    CochainComplex (ModuleCat S) ℤ ⥤ CochainComplex (ModuleCat S') ℤ :=
  (ModuleCat.extendScalars σ).mapHomologicalComplex (up ℤ)

/-- Termwise extension of a lower-bounded cochain complex remains lower-bounded after passage to
the derived category. -/
@[stacks 0FUY "scalar extension preserves lower support"]
theorem targetIsGE
    (P : CochainComplex (ModuleCat S) ℤ)
    (hP : CochainComplex.IsStrictlyGE P (-1)) :
    t.IsGE
      (DerivedCategory.Q.obj
        ((scalarExtendedCochain (algebraMap S S')).obj P)) (-1) := sorry
/- Proof strategy: strict support is preserved degreewise by `ModuleCat.extendScalars`; apply the
canonical `DerivedCategory.Q` support lemma to the scalar-extended complex and rewrite the bound
with `hP`. -/

/-- The canonical derived-to-underived scalar-extension comparison on a cochain complex. -/
@[stacks 0FUY "derived-to-underived scalar-extension comparison"]
noncomputable def comparison (P : CochainComplex (ModuleCat S) ℤ) :
    (ModuleCat.derivedExtensionOfScalars (algebraMap S S')).obj
        (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        ((scalarExtendedCochain (algebraMap S S')).obj P) :=
  (ModuleCat.derivedExtensionComplexCounit (algebraMap S S')).app P

/-- The comparison obtained by applying the canonical lower truncation functor at degree `-1`.

The codomain is also truncated here so that the morphism data does not depend on a proof that the
termwise scalar extension is already in degrees `≥ -1`; `targetIsGE` supplies that separate
source-semantic fact. -/
@[stacks 0FUY "lower-truncated scalar-extension comparison"]
noncomputable def truncGEComparison (P : CochainComplex (ModuleCat S) ℤ) :
    (t.truncGE (-1)).obj
        ((ModuleCat.derivedExtensionOfScalars (algebraMap S S')).obj
          (DerivedCategory.Q.obj P)) ⟶
      (t.truncGE (-1)).obj
        (DerivedCategory.Q.obj
          ((scalarExtendedCochain (algebraMap S S')).obj P)) :=
  (t.truncGE (-1)).map (comparison (S := S) (S' := S') P)

/-- The canonical termwise base change of `NL{S⁄R}` lies in degrees `≥ -1`. -/
@[stacks 0FUY "self-presentation underived target concentration"]
theorem selfTargetIsGE :
    t.IsGE
      (DerivedCategory.Q.obj
        ((scalarExtendedCochain (algebraMap S S')).obj
          ((Algebra.naiveCotangent R S).extend embeddingDownNat))) (-1) := sorry
/- Proof strategy: apply `targetIsGE` to the canonical self-presentation of the naive cotangent
complex, using its strict concentration in cochain degrees `-1` and `0`. -/

/-- The derived-to-underived base-change comparison for the canonical naive cotangent object
`NL{S⁄R}`. -/
@[stacks 0FUY "self-presentation base-change comparison"]
noncomputable def selfComparison :
    (Algebra.naiveCotangentObject R S ⊗[S]^L[S']) ⟶
      DerivedCategory.Q.obj
        ((scalarExtendedCochain (algebraMap S S')).obj
          ((Algebra.naiveCotangent R S).extend embeddingDownNat)) :=
  comparison (S := S) (S' := S')
    ((Algebra.naiveCotangent R S).extend embeddingDownNat)

/-- The lower-truncated base-change comparison for the canonical naive cotangent object. -/
@[stacks 0FUY "self-presentation lower-truncated comparison"]
noncomputable def selfTruncGEComparison :
    (t.truncGE (-1)).obj (Algebra.naiveCotangentObject R S ⊗[S]^L[S']) ⟶
      (t.truncGE (-1)).obj
        (DerivedCategory.Q.obj
          ((scalarExtendedCochain (algebraMap S S')).obj
            ((Algebra.naiveCotangent R S).extend embeddingDownNat))) :=
  truncGEComparison (S := S) (S' := S')
    ((Algebra.naiveCotangent R S).extend embeddingDownNat)

/-- After lower truncation at degree `-1`, the canonical
derived-to-underived base-change comparison for `NL{S⁄R}` is an isomorphism. -/
@[stacks 0FUY "(1), self-presentation truncation comparison"]
instance selfTruncGEComparison_isIso :
    IsIso (selfTruncGEComparison (R := R) (S := S) (S' := S')) := sorry
/- Proof strategy: identify `selfTruncGEComparison` with truncation of
`ModuleCat.derivedExtensionComplexCounit`.  The cone of the counit has no cohomology in degrees
`≥ -1` for the two-term self-presentation, so the t-structure truncation criterion makes the
comparison an isomorphism. -/

/-- The termwise base change of the naive cotangent complex of a chosen presentation lies in
degrees `≥ -1`. -/
@[stacks 0FUY "presentation underived target concentration"]
theorem presentationTargetIsGE (P : Presentation R S ι κ) :
    t.IsGE
      (DerivedCategory.Q.obj
        ((scalarExtendedCochain (algebraMap S S')).obj
          ((Extension.NaiveCotangent.complex P.toExtension).extend embeddingDownNat))) (-1) := sorry
/- Proof strategy: apply `targetIsGE`; the presentation-level naive cotangent complex is strictly
supported in degrees `-1` and `0`, and extension along `embeddingDownNat` preserves that support. -/

/-- The derived-to-underived base-change comparison for the naive cotangent complex of a chosen
presentation. -/
@[stacks 0FUY "presentation base-change comparison"]
noncomputable def presentationComparison (P : Presentation R S ι κ) :
    (DerivedCategory.Q.obj
        ((Extension.NaiveCotangent.complex P.toExtension).extend embeddingDownNat) ⊗[S]^L[S']) ⟶
      DerivedCategory.Q.obj
        ((scalarExtendedCochain (algebraMap S S')).obj
          ((Extension.NaiveCotangent.complex P.toExtension).extend embeddingDownNat)) :=
  comparison (S := S) (S' := S')
    ((Extension.NaiveCotangent.complex P.toExtension).extend embeddingDownNat)

/-- The lower-truncated base-change comparison for the naive cotangent complex of a chosen
presentation. -/
@[stacks 0FUY "presentation lower-truncated comparison"]
noncomputable def presentationTruncGEComparison (P : Presentation R S ι κ) :
    (t.truncGE (-1)).obj
        (DerivedCategory.Q.obj
          ((Extension.NaiveCotangent.complex P.toExtension).extend embeddingDownNat) ⊗[S]^L[S']) ⟶
      (t.truncGE (-1)).obj
        (DerivedCategory.Q.obj
          ((scalarExtendedCochain (algebraMap S S')).obj
            ((Extension.NaiveCotangent.complex P.toExtension).extend embeddingDownNat))) :=
  truncGEComparison (S := S) (S' := S')
    ((Extension.NaiveCotangent.complex P.toExtension).extend embeddingDownNat)

/-- After lower truncation at degree `-1`, the canonical
derived-to-underived base-change comparison for any chosen presentation is an isomorphism. -/
@[stacks 0FUY "(2), presentation truncation comparison"]
instance presentationTruncGEComparison_isIso (P : Presentation R S ι κ) :
    IsIso (presentationTruncGEComparison (S' := S') P) := sorry
/- Proof strategy: repeat the counit-cone argument for the chosen presentation.  Use the explicit
two-term presentation model to show that the cone is below degree `-1`, then invoke the
t-structure truncation isomorphism criterion. -/

end Algebra.NaiveCotangent.DerivedBaseChange
