module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.BaseChange.Tensor
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.Relative
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor-product base change of structured RHom models

This integration leaf connects the relative model producers with the generic tensor-product
base-change theorem.  The lower leaves remain independent: relative model construction does not
depend on base change, and the generic base-change theorem does not depend on a particular model
producer.
@stack 0E1U
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CochainComplex.HomComplex
open scoped TensorProduct Algebra.TensorProduct.Right

namespace CategoryTheory.DerivedCategory.InternalHom.RHom

namespace FiniteTorModel

variable {R A R' : Type u}
variable [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R'] [Module.Flat R A]
variable {K L : DerivedCategory (ModuleCat A)}

/-- A structured finite-Tor `RHom` model remains a canonical `RHom` model after arbitrary
tensor-product base change of the coefficient ring (Lemma 15.84.6, Stacks `0E1U`). -/
@[stacks 0E1U "tensor-product base change of a structured RHom model"]
theorem baseChange (M : FiniteTorModel R K L) :
    IsIsomorphic
      (DerivedCategory.Q.obj
        (ModuleCat.Pushout.Tensor.algebraBaseChange
          (moduleComplex A M.source M.target)))
      (obj (A := A ⊗[R] R')
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap A (A ⊗[R] R'))).obj K)
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap A (A ⊗[R] R'))).obj L)) :=
  CochainComplex.HomComplex.Pushout.Tensor.representsRHom_of_finiteFree
    M.source M.target M.sourceIso M.targetIso M.sourceMinus M.sourceFiniteFree
      M.targetBounded M.targetFlat

end FiniteTorModel

namespace PerfectModel

variable {R A R' : Type u}
variable [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R'] [Module.Flat R A]
variable {K L : DerivedCategory (ModuleCat A)}

/-- Tensor-product base change of a relative-perfect `RHom` model, through its finite-Tor
model projection. -/
@[stacks 0E1U "tensor-product base change of a relative-perfect RHom model"]
abbrev baseChange (M : PerfectModel R K L) :
    IsIsomorphic
      (DerivedCategory.Q.obj
        (ModuleCat.Pushout.Tensor.algebraBaseChange
          (moduleComplex A M.source M.target)))
      (obj (A := A ⊗[R] R')
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap A (A ⊗[R] R'))).obj K)
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap A (A ⊗[R] R'))).obj L)) :=
  FiniteTorModel.baseChange (R' := R') M.toFiniteTorModel

end PerfectModel

end CategoryTheory.DerivedCategory.InternalHom.RHom
