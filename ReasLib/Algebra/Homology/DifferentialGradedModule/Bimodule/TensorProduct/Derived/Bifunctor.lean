/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.Naturality
public import ReasLib.CategoryTheory.Localization.Lifting.CommShift

/-!
# Derived Tensor Product as a Bifunctor

Total derived tensor product is covariant in a bimodule. This file descends the strict
bimodule parameter once to the full derived bimodule category and exposes the localization
factorization used by all later consumers.
-/

@[expose] public section

noncomputable section

universe u v w x y

open CategoryTheory

namespace DifferentialGradedBimodule.Tensor

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, x} R} {B : CochainDGAlgebra.{u, y} R}

set_option maxHeartbeats 1000000 in
/-- Total derived tensor product, functorial in the full derived category of (A, B)-bimodules. -/
@[stacks 09S3 "derived tensor on the derived bimodule category"]
noncomputable def derivedBifunctor (A : CochainDGAlgebra.{u, x} R)
    (B : CochainDGAlgebra.{u, y} R) :
    DifferentialGradedBimodule.Derived.Category.{u, w, x, y} A B ⥤
      (DifferentialGradedModule.Derived.Category.{u, v} A ⥤
        DifferentialGradedModule.Derived.Category.{u, max v w} B) :=
  Localization.lift (derivedBimoduleFunctor.{u, v, w, x, y} A B)
    (derivedBimoduleFunctor_inverts.{u, x, y, w, v} A B)
    (DifferentialGradedBimodule.Derived.fromBimodules.{u, w, x, y} A B)

set_option maxHeartbeats 1000000 in
/-- Pulling derivedBifunctor back to strict bimodules recovers the strict tensor parameter
functor. -/
@[stacks 09S3 "strict factorization of derived tensor"]
noncomputable def derivedBifunctorFactors (A : CochainDGAlgebra.{u, x} R)
    (B : CochainDGAlgebra.{u, y} R) :
    DifferentialGradedBimodule.Derived.fromBimodules.{u, w, x, y} A B ⋙
        derivedBifunctor.{u, v, w, x, y} A B ≅
      derivedBimoduleFunctor.{u, v, w, x, y} A B :=
  Localization.fac (derivedBimoduleFunctor.{u, v, w, x, y} A B)
    (derivedBimoduleFunctor_inverts.{u, x, y, w, v} A B)
    (DifferentialGradedBimodule.Derived.fromBimodules.{u, w, x, y} A B)

/-- derivedBifunctor is the chosen localization lift of the strict derived tensor parameter
functor. -/
@[stacks 09S3 "localization lift of the derived tensor parameter"]
noncomputable instance derivedBifunctorLifting
    (A : CochainDGAlgebra.{u, x} R) (B : CochainDGAlgebra.{u, y} R) :
    Localization.Lifting
      (DifferentialGradedBimodule.Derived.fromBimodules.{u, w, x, y} A B)
      (DifferentialGradedBimodule.quasiIso A B)
      (derivedBimoduleFunctor.{u, v, w, x, y} A B)
      (derivedBifunctor.{u, v, w, x, y} A B) :=
  ⟨derivedBifunctorFactors.{u, v, w, x, y} A B⟩

/-- Derived tensor product is additive in its derived-bimodule variable. -/
@[stacks 09S3 "additivity of derived tensor in the derived bimodule"]
noncomputable instance derivedBifunctorAdditive
    (A : CochainDGAlgebra.{u, x} R) (B : CochainDGAlgebra.{u, y} R) :
    (derivedBifunctor.{u, v, w, x, y} A B).Additive := sorry

/-- Derived tensor product is R-linear in its derived-bimodule variable. -/
@[stacks 09S3 "linearity of derived tensor in the derived bimodule"]
noncomputable instance derivedBifunctorLinear
    (A : CochainDGAlgebra.{u, x} R) (B : CochainDGAlgebra.{u, y} R) :
    Functor.Linear R (derivedBifunctor.{u, v, w, x, y} A B) := sorry

/-- Fixing a derived bimodule in derivedBifunctor gives an additive tensor functor. -/
@[stacks 09S3 "additivity of derived tensor at a derived bimodule"]
noncomputable instance derivedBifunctorObjAdditive
    (N : DifferentialGradedBimodule.Derived.Category.{u, w, x, y} A B) :
    ((derivedBifunctor.{u, v, w, x, y} A B).obj N).Additive := sorry

/-- Fixing a derived bimodule in derivedBifunctor gives an R-linear tensor functor. -/
@[stacks 09S3 "linearity of derived tensor at a derived bimodule"]
noncomputable instance derivedBifunctorObjLinear
    (N : DifferentialGradedBimodule.Derived.Category.{u, w, x, y} A B) :
    Functor.Linear R ((derivedBifunctor.{u, v, w, x, y} A B).obj N) := sorry

/-- Fixing a derived bimodule gives a tensor functor that commutes with integer shifts. -/
@[stacks 09S3 "shift compatibility of derived tensor at a derived bimodule"]
noncomputable instance derivedBifunctorObjCommShift
    (N : DifferentialGradedBimodule.Derived.Category.{u, w, x, y} A B) :
    ((derivedBifunctor.{u, v, w, x, y} A B).obj N).CommShift ℤ :=
  Localization.Lifting.objCommShift
    (L := DifferentialGradedBimodule.Derived.fromBimodules.{u, w, x, y} A B)
    (W := DifferentialGradedBimodule.quasiIso A B)
    (F := derivedBimoduleFunctor.{u, v, w, x, y} A B)
    (F' := derivedBifunctor.{u, v, w, x, y} A B)
    (fun X ↦ derivedFunctor_commShift.{u, v, w, x, y} X) N

/-- Fixing a derived bimodule gives a triangulated derived tensor functor. -/
@[stacks 09S3 "triangulated derived tensor at a derived bimodule"]
instance derivedBifunctorObjIsTriangulated
    (N : DifferentialGradedBimodule.Derived.Category.{u, w, x, y} A B) :
    ((derivedBifunctor.{u, v, w, x, y} A B).obj N).IsTriangulated := sorry

/-- At the derived image of a strict bimodule, derivedBifunctor recovers tensoring by that
bimodule. -/
@[stacks 09S3 "derived tensor at a strict bimodule"]
noncomputable def derivedBifunctorObjIso
    (N : DifferentialGradedBimodule.{u, w, x, y} A B) :
    (derivedBifunctor.{u, v, w, x, y} A B).obj
        (DifferentialGradedBimodule.Derived.object.{u, w, x, y} N) ≅
      derivedFunctor.{u, v, w, x, y} N :=
  (derivedBifunctorFactors.{u, v, w, x, y} A B).app N

/-- The forward strict-representative comparison is natural in a bimodule morphism. -/
@[reassoc (attr := simp), stacks 09S3 "naturality of the strict derived tensor comparison"]
theorem derivedBifunctorObjIso.hom_naturality
    {N N' : DifferentialGradedBimodule.{u, w, x, y} A B} (f : N ⟶ N') :
    (derivedBifunctor.{u, v, w, x, y} A B).map
          ((DifferentialGradedBimodule.Derived.fromBimodules.{u, w, x, y} A B).map f) ≫
        (derivedBifunctorObjIso N').hom =
      (derivedBifunctorObjIso N).hom ≫ derivedNatTrans f := sorry

/-- The inverse strict-representative comparison is natural in a bimodule morphism. -/
@[reassoc (attr := simp), stacks 09S3 "inverse naturality of the strict derived tensor comparison"]
theorem derivedBifunctorObjIso.inv_naturality
    {N N' : DifferentialGradedBimodule.{u, w, x, y} A B} (f : N ⟶ N') :
    derivedNatTrans f ≫ (derivedBifunctorObjIso N').inv =
      (derivedBifunctorObjIso N).inv ≫
        (derivedBifunctor.{u, v, w, x, y} A B).map
          ((DifferentialGradedBimodule.Derived.fromBimodules.{u, w, x, y} A B).map f) := sorry

/-- On a strict bimodule morphism, the descended action is conjugate to the canonical derived
tensor transformation by the factorization isomorphisms. -/
@[stacks 09S3 "derived tensor on a strict bimodule morphism"]
theorem derivedBifunctor_map_fromBimodules
    {N N' : DifferentialGradedBimodule.{u, w, x, y} A B} (f : N ⟶ N') :
    (derivedBifunctor.{u, v, w, x, y} A B).map
        ((DifferentialGradedBimodule.Derived.fromBimodules.{u, w, x, y} A B).map f) =
      (derivedBifunctorObjIso N).hom ≫ derivedNatTrans f ≫
        (derivedBifunctorObjIso N').inv := sorry

variable (N : DifferentialGradedBimodule.Derived.Category.{u, w, x, y} A B)

#synth (derivedBifunctor.{u, v, w, x, y} A B).Additive
#synth Functor.Linear R (derivedBifunctor.{u, v, w, x, y} A B)
#synth ((derivedBifunctor.{u, v, w, x, y} A B).obj N).Additive
#synth Functor.Linear R ((derivedBifunctor.{u, v, w, x, y} A B).obj N)
#synth ((derivedBifunctor.{u, v, w, x, y} A B).obj N).CommShift ℤ
#synth ((derivedBifunctor.{u, v, w, x, y} A B).obj N).IsTriangulated

end DifferentialGradedBimodule.Tensor
