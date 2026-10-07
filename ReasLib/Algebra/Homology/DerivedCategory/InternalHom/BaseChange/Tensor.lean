module

public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Pushout.Tensor
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.ScalarExtension.Pushout.Tensor
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.BaseChange
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Internal-Hom models after tensor-product base change

This leaf specializes the pushout internal-Hom comparison to the canonical square
`R → A`, `R → R'`, `A' = A ⊗[R] R'`.  It uses the shared scoped right tensor-algebra owner so
consumers can use the specialization without rebuilding local algebra instances.
@stack 0E1U
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.DerivedCategory
open CochainComplex.HomComplex
open scoped TensorProduct Algebra.TensorProduct.Right

namespace CochainComplex.HomComplex.Pushout.Tensor

variable {R A R' : Type u}
variable [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']

/-- For the canonical tensor-product pushout, separate upper and lower bounds together with
relative termwise flatness give a scalar-extended model of canonical derived `RHom` (Lemma 15.85.6,
Stacks `0E1U`). -/
@[stacks 0E1U "canonical RHom model after tensor-product pushout"]
theorem representsRHom
    {K L : DerivedCategory (ModuleCat.{u} A)} (P F : CochainComplex (ModuleCat A) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ K) (eF : DerivedCategory.Q.obj F ≅ L)
    (hP : CochainComplex.minus (ModuleCat A) P) (hPfp : P.IsTermwiseFiniteProjective)
    (hFminus : CochainComplex.minus (ModuleCat A) F) (hFplus : CochainComplex.plus (ModuleCat A) F)
    (hFflat : F.IsTermwiseFlatOver R) :
    IsIsomorphic
      (DerivedCategory.Q.obj (ModuleCat.Pushout.Tensor.algebraBaseChange (moduleComplex A P F)))
      (CategoryTheory.DerivedCategory.InternalHom.RHom.obj (A := A ⊗[R] R')
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap A (A ⊗[R] R'))).obj K)
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap A (A ⊗[R] R'))).obj L)) :=
  CochainComplex.HomComplex.Pushout.representsRHom
    (R' := R') (A' := A ⊗[R] R') P F eP eF hP hPfp hFminus hFplus hFflat
/- Proof strategy: specialize `CochainComplex.HomComplex.Pushout.representsRHom` to
`A' := A ⊗[R] R'` and discharge its square using the canonical tensor-product `Algebra.IsPushout`. -/

/-- The bounded-target specialization of the tensor-product pushout comparison (Lemma 15.85.6,
Stacks `0E1U`). -/
@[stacks 0E1U "bounded canonical RHom model after tensor-product pushout"]
theorem representsRHom_of_bounded
    {K L : DerivedCategory (ModuleCat.{u} A)} (P F : CochainComplex (ModuleCat A) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ K) (eF : DerivedCategory.Q.obj F ≅ L)
    (hP : CochainComplex.minus (ModuleCat A) P) (hPfp : P.IsTermwiseFiniteProjective)
    (hF : CochainComplex.bounded (ModuleCat A) F) (hFflat : F.IsTermwiseFlatOver R) :
    IsIsomorphic
      (DerivedCategory.Q.obj (ModuleCat.Pushout.Tensor.algebraBaseChange (moduleComplex A P F)))
      (CategoryTheory.DerivedCategory.InternalHom.RHom.obj (A := A ⊗[R] R')
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap A (A ⊗[R] R'))).obj K)
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap A (A ⊗[R] R'))).obj L)) := by
  obtain ⟨hFplus, hFminus⟩ := (CochainComplex.bounded_iff (ModuleCat A) F).mp hF
  exact representsRHom P F eP eF hP hPfp hFminus hFplus hFflat
/- Proof strategy: split `hF` with
`(CochainComplex.bounded_iff (ModuleCat A) F).mp hF`, then apply the preceding tensor pushout
theorem and retain the canonical right tensor-algebra scope. -/

/- The source-facing interface starts from the finite-free representative delivered by the
relative model producer.  The finite-projective obligation is an inference detail of the
internal-Hom computation, not mathematical input that downstream users should rebuild. -/
/-- A bounded-above finite-free source model and a bounded relatively flat target model have a Hom
complex whose canonical tensor-product base change represents the derived internal Hom after any
`R → R'` (Lemma 15.85.6, Stacks `0E1U`). -/
@[stacks 0E1U "finite-free canonical RHom model after arbitrary tensor-product base change"]
theorem representsRHom_of_finiteFree
    [Module.Flat R A] {K L : DerivedCategory (ModuleCat.{u} A)}
    (P F : CochainComplex (ModuleCat A) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ K) (eF : DerivedCategory.Q.obj F ≅ L)
    (hP : CochainComplex.minus (ModuleCat A) P) (hPfree : P.IsTermwiseFiniteFree)
    (hF : CochainComplex.bounded (ModuleCat A) F) (hFflat : F.IsTermwiseFlatOver R) :
    IsIsomorphic
      (DerivedCategory.Q.obj (ModuleCat.Pushout.Tensor.algebraBaseChange (moduleComplex A P F)))
      (CategoryTheory.DerivedCategory.InternalHom.RHom.obj (A := A ⊗[R] R')
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap A (A ⊗[R] R'))).obj K)
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap A (A ⊗[R] R'))).obj L)) :=
  representsRHom_of_bounded P F eP eF hP
    (HomologicalComplex.IsTermwiseFiniteProjective.of_finiteFree hPfree) hF hFflat
/- Proof strategy: obtain the canonical termwise finite-projective interface from `hPfree`, then
apply `representsRHom_of_bounded`; `ModuleCat.Pushout.Tensor.cochainIso` exposes the
source's `E ⊗[R] R'` view after restriction to `R'`, while `algebraBaseChange` remains the canonical
`A ⊗[R] R'`-valued complex in the conclusion. -/

/-- Source-facing compatibility name for tensor-product pushout base change of an `RHom` model. -/
@[stacks 0E1U "internal-Hom model after tensor-product pushout"]
abbrev representsInternalHom
    {K L : DerivedCategory (ModuleCat.{u} A)} (P F : CochainComplex (ModuleCat A) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ K) (eF : DerivedCategory.Q.obj F ≅ L)
    (hP : CochainComplex.minus (ModuleCat A) P) (hPfp : P.IsTermwiseFiniteProjective)
    (hFminus : CochainComplex.minus (ModuleCat A) F)
    (hFplus : CochainComplex.plus (ModuleCat A) F) (hFflat : F.IsTermwiseFlatOver R) :
    IsIsomorphic
      (DerivedCategory.Q.obj (ModuleCat.Pushout.Tensor.algebraBaseChange (moduleComplex A P F)))
      (CategoryTheory.DerivedCategory.InternalHom.RHom.obj (A := A ⊗[R] R')
        ((ModuleCat.derivedExtensionOfScalars (algebraMap A (A ⊗[R] R'))).obj K)
        ((ModuleCat.derivedExtensionOfScalars (algebraMap A (A ⊗[R] R'))).obj L)) :=
  representsRHom P F eP eF hP hPfp hFminus hFplus hFflat

/-- Source-facing compatibility name for bounded tensor-product pushout base change of an `RHom` model. -/
@[stacks 0E1U "bounded internal-Hom model after tensor-product pushout"]
abbrev representsInternalHom_of_bounded
    {K L : DerivedCategory (ModuleCat.{u} A)} (P F : CochainComplex (ModuleCat A) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ K) (eF : DerivedCategory.Q.obj F ≅ L)
    (hP : CochainComplex.minus (ModuleCat A) P) (hPfp : P.IsTermwiseFiniteProjective)
    (hF : CochainComplex.bounded (ModuleCat A) F) (hFflat : F.IsTermwiseFlatOver R) :
    IsIsomorphic
      (DerivedCategory.Q.obj (ModuleCat.Pushout.Tensor.algebraBaseChange (moduleComplex A P F)))
      (CategoryTheory.DerivedCategory.InternalHom.RHom.obj (A := A ⊗[R] R')
        ((ModuleCat.derivedExtensionOfScalars (algebraMap A (A ⊗[R] R'))).obj K)
        ((ModuleCat.derivedExtensionOfScalars (algebraMap A (A ⊗[R] R'))).obj L)) :=
  representsRHom_of_bounded P F eP eF hP hPfp hF hFflat

/-- Source-facing compatibility name for the finite-free tensor-product pushout computation of `RHom`. -/
@[stacks 0E1U "finite-free internal-Hom model after tensor-product pushout"]
abbrev representsInternalHom_of_finiteFree
    [Module.Flat R A] {K L : DerivedCategory (ModuleCat.{u} A)}
    (P F : CochainComplex (ModuleCat A) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ K) (eF : DerivedCategory.Q.obj F ≅ L)
    (hP : CochainComplex.minus (ModuleCat A) P) (hPfree : P.IsTermwiseFiniteFree)
    (hF : CochainComplex.bounded (ModuleCat A) F) (hFflat : F.IsTermwiseFlatOver R) :
    IsIsomorphic
      (DerivedCategory.Q.obj (ModuleCat.Pushout.Tensor.algebraBaseChange (moduleComplex A P F)))
      (CategoryTheory.DerivedCategory.InternalHom.RHom.obj (A := A ⊗[R] R')
        ((ModuleCat.derivedExtensionOfScalars (algebraMap A (A ⊗[R] R'))).obj K)
        ((ModuleCat.derivedExtensionOfScalars (algebraMap A (A ⊗[R] R'))).obj L)) :=
  representsRHom_of_finiteFree P F eP eF hP hPfree hF hFflat

end CochainComplex.HomComplex.Pushout.Tensor
