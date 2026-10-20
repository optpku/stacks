/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorHom.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorHom.Naturality
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.Naturality
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Derived.Naturality
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Naturality

/-!
# Naturality of the Derived DG Tensor-Hom Adjunction

The canonical transformations obtained by deriving tensor maps and internal-Hom precomposition
remain mates.  The accompanying forward and inverse formulas expose this compatibility directly
through the derived tensor-Hom equivalence.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open DifferentialGradedCategory

universe u v w x

namespace DifferentialGradedBimodule.TensorHom

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, x} R}

/-- Derived tensor-Hom currying is contravariantly natural in the DG bimodule parameter. -/
@[stacks 09LT "naturality of the derived tensor-Hom adjunction in the bimodule"]
theorem derivedHomEquiv_naturality_middle
    {N N' : DifferentialGradedBimodule.{u, v, w, x} A B} (f : N ⟶ N')
    (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    (P : DifferentialGradedModule.Derived.Category.{u, v} B)
    (g : (Tensor.derivedFunctor.{u, v, v, w, x} N').obj M ⟶ P) :
    derivedHomEquiv.{u, v} N M P ((Tensor.derivedNatTrans.{u, v, v, w, x} f).app M ≫ g) =
      derivedHomEquiv.{u, v} N' M P g ≫ (InternalHom.derivedNatTrans.{u, v} f).app P := sorry

/-- Derived tensor-Hom uncurrying is contravariantly natural in the DG bimodule parameter. -/
@[stacks 09LT "naturality of derived tensor-Hom uncurrying in the bimodule"]
theorem derivedHomEquiv_symm_naturality_middle
    {N N' : DifferentialGradedBimodule.{u, v, w, x} A B} (f : N ⟶ N')
    (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    (P : DifferentialGradedModule.Derived.Category.{u, v} B)
    (g : M ⟶ (InternalHom.derivedFunctor.{u, v} N').obj P) :
    (derivedHomEquiv.{u, v} N M P).symm (g ≫ (InternalHom.derivedNatTrans.{u, v} f).app P) =
      (Tensor.derivedNatTrans.{u, v, v, w, x} f).app M ≫ (derivedHomEquiv.{u, v} N' M P).symm g := sorry

/-- Linear derived tensor-Hom currying is contravariantly natural in the DG bimodule
parameter. -/
@[stacks 09LT "naturality of linear derived tensor-Hom currying in the bimodule"]
theorem derivedHomLinearEquiv_naturality_middle
    {N N' : DifferentialGradedBimodule.{u, v, w, x} A B} (f : N ⟶ N')
    (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    (P : DifferentialGradedModule.Derived.Category.{u, v} B)
    (g : (Tensor.derivedFunctor.{u, v, v, w, x} N').obj M ⟶ P) :
    derivedHomLinearEquiv.{u, v} N M P ((Tensor.derivedNatTrans.{u, v, v, w, x} f).app M ≫ g) =
      derivedHomLinearEquiv.{u, v} N' M P g ≫
        (InternalHom.derivedNatTrans.{u, v} f).app P := sorry

/-- Linear derived tensor-Hom uncurrying is contravariantly natural in the DG bimodule
parameter. -/
@[stacks 09LT "naturality of linear derived tensor-Hom uncurrying in the bimodule"]
theorem derivedHomLinearEquiv_symm_naturality_middle
    {N N' : DifferentialGradedBimodule.{u, v, w, x} A B} (f : N ⟶ N')
    (M : DifferentialGradedModule.Derived.Category.{u, v} A)
    (P : DifferentialGradedModule.Derived.Category.{u, v} B)
    (g : M ⟶ (InternalHom.derivedFunctor.{u, v} N').obj P) :
    (derivedHomLinearEquiv.{u, v} N M P).symm
        (g ≫ (InternalHom.derivedNatTrans.{u, v} f).app P) =
      (Tensor.derivedNatTrans.{u, v, v, w, x} f).app M ≫
        (derivedHomLinearEquiv.{u, v} N' M P).symm g := sorry

namespace Derived

/-- Derived internal-Hom precomposition is the mate of the corresponding derived tensor
transformation in the DG bimodule parameter. -/
@[stacks 09LT "mate compatibility of derived tensor and internal Hom"]
theorem precomp_eq_conjugateEquiv
    {N N' : DifferentialGradedBimodule.{u, v, w, x} A B} (f : N ⟶ N') :
    InternalHom.derivedNatTrans.{u, v} f =
      conjugateEquiv (derivedAdjunction.{u, v} N') (derivedAdjunction.{u, v} N)
        (Tensor.derivedNatTrans.{u, v, v, w, x} f) := sorry

end Derived

end DifferentialGradedBimodule.TensorHom
