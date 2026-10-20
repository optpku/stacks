/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.Bifunctor
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory
open DifferentialGradedBimodule

universe u v w x y

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, x} R} {B : CochainDGAlgebra.{u, y} R}
variable {N N' : DifferentialGradedBimodule.{u, w, x, y} A B}
variable (f : N ⟶ N') (e : N ≅ N')

/-!
# Lemma 22.33.3 (09S3)

The reusable owner constructs the tensor map in the bimodule variable before passing through
the intrinsic homotopy and derived categories.
-/

/- Lemma 22.33.3 (09S3): a bimodule morphism induces the canonical transformation between
total left-derived tensor functors. -/
@[stacks 09S3]
#check
  (Tensor.derivedNatTrans.{u, v, w, x, y} f :
    Tensor.derivedFunctor.{u, v, w, x, y} N ⟶
      Tensor.derivedFunctor.{u, v, w, x, y} N')

/- A bimodule quasi-isomorphism induces an isomorphism of derived tensor functors. -/
#check @DifferentialGradedBimodule.Tensor.derivedNatTrans_isIso_of_quasiIso

/- The construction is owned by explicit maps on tensor quotients and their homotopy-category
natural transformations. -/
#check @DifferentialGradedBimodule.Tensor.mapBimodule
#check @DifferentialGradedBimodule.Tensor.mapBimodule_tmul
#check @DifferentialGradedBimodule.Tensor.sourceK
#check @DifferentialGradedBimodule.Tensor.sourceK_id
#check @DifferentialGradedBimodule.Tensor.sourceK_comp

/- A strict bimodule isomorphism and both of its maps are carried through the source and total
derived comparison layers. -/
#check DifferentialGradedBimodule.Tensor.derivedSourceIso_inv e
#check DifferentialGradedBimodule.Tensor.derivedNatIso_hom e
#check DifferentialGradedBimodule.Tensor.derivedNatIso_inv e

/- The enrichment laws are owned once by total left derivation; the tensor statements below
are its covariant parameter specialization. -/
#check @CategoryTheory.Functor.LeftDerived.mapNatTrans.zero
#check @CategoryTheory.Functor.LeftDerived.mapNatTrans.add
#check @CategoryTheory.Functor.LeftDerived.mapNatTrans.smul

/- The full family of derived tensor functors is additive and linear in the bimodule parameter. -/
#check @DifferentialGradedBimodule.Tensor.derivedSourceMap_zero
#check @DifferentialGradedBimodule.Tensor.derivedSourceMap_add
#check @DifferentialGradedBimodule.Tensor.derivedSourceMap_smul
#check @DifferentialGradedBimodule.Tensor.derivedNatTrans_zero
#check @DifferentialGradedBimodule.Tensor.derivedNatTrans_add
#check @DifferentialGradedBimodule.Tensor.derivedNatTrans_smul
#check @DifferentialGradedBimodule.Tensor.derivedBimoduleFunctor
#check @DifferentialGradedBimodule.Tensor.derivedBimoduleFunctor_obj
#check @DifferentialGradedBimodule.Tensor.derivedBimoduleFunctor_map
#check @DifferentialGradedBimodule.Tensor.derivedBimoduleFunctor_inverts

#synth (Tensor.derivedBimoduleFunctor.{u, v, w, x, y} A B).Additive
#synth CategoryTheory.Functor.Linear R
  (Tensor.derivedBimoduleFunctor.{u, v, w, x, y} A B)

/- The stable library owner is covariant on the full derived category of bimodules and records
its comparison with strict representatives. -/
#check @DifferentialGradedBimodule.Tensor.derivedBifunctor
#check @DifferentialGradedBimodule.Tensor.derivedBifunctorFactors
#check Tensor.derivedBifunctorObjIso.{u, v, w, x, y} N
#check Tensor.derivedBifunctorObjIso.hom_naturality.{u, v, w, x, y} f
#check Tensor.derivedBifunctorObjIso.inv_naturality.{u, v, w, x, y} f
#check Tensor.derivedBifunctor_map_fromBimodules.{u, v, w, x, y} f

#synth (Tensor.derivedBifunctor.{u, v, w, x, y} A B).Additive
#synth CategoryTheory.Functor.Linear R
  (Tensor.derivedBifunctor.{u, v, w, x, y} A B)

/- Property-P representatives expose the quasi-isomorphism-to-`IsIso` bridge used in the
derived argument. -/
#check @DifferentialGradedBimodule.Tensor.mapBimodule_quasiIso_of_hasPropertyP
#check @DifferentialGradedBimodule.Tensor.derivedSourceMap_app_isIso_of_hasPropertyP
#check @DifferentialGradedBimodule.Tensor.derivedNatTrans_app_isIso_of_hasPropertyP
