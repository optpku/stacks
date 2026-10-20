/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Extension
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Restriction

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleValuedFunctor.TensorLinearlyAdequate

/-- A short exact sequence in tensor-adequate module-valued functors with tensor-linearly
adequate quotient has split-epimorphic quotient map. -/
theorem shortExact_isSplitEpi
    {A : CommRingCat.{u}} {F G L : ModuleValuedFunctor.TensorAdeq A}
    (i : F.obj ⟶ G.obj) (p : G.obj ⟶ L.obj)
    (h_zero : i ≫ p =
      (@HasZeroMorphisms.zero (ModuleValuedFunctor.bundled A) _
        (ModuleValuedFunctor.bundledHasZeroMorphisms A) F.obj L.obj).zero)
    (h_short :
      @ShortComplex.ShortExact (ModuleValuedFunctor.bundled A) _
        (ModuleValuedFunctor.bundledHasZeroMorphisms A)
        (@ShortComplex.mk (ModuleValuedFunctor.bundled A) _
          (ModuleValuedFunctor.bundledHasZeroMorphisms A) _ _ _ i p h_zero))
    (hL : ModuleValuedFunctor.TensorLinearlyAdequate L.obj) :
    IsSplitEpi p := sorry

/-- A tensor-linearly adequate object of the tensor-adequate category is projective. -/
theorem projective {A : CommRingCat.{u}} (L : ModuleValuedFunctor.TensorAdeq A)
    (hL : ModuleValuedFunctor.TensorLinearlyAdequate L.obj) :
    CategoryTheory.Projective L := sorry

end ModuleValuedFunctor.TensorLinearlyAdequate
