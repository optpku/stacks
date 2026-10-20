/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Countability
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.DerivedCategory
open scoped DerivedExt

noncomputable section

universe u

/- Lemma 36.33.2 (1): if every cohomology sheaf of `K : D_QCoh(𝒪_X)` has
countable sections on affine opens, then the hypercohomology of `K ⊗ᴸ E` on any
quasi-compact open is countable for every perfect `E`. -/
@[stacks 0CRP] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.tensorOpenHypercohomologyCountable :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (K : AlgebraicGeometry.Scheme.DerivedQCoh X)
    (hK : ∀ j : ℤ, ∀ V : X.affineOpens,
      Countable (RingedSpace.moduleSectionsOnOpen
        (RingedSpace.ModuleDerived.cohomologySheaf K.obj j) (V : X.Opens)))
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E) (U : X.Opens)
    (hU : IsCompact (U : Set X)) (i : ℤ),
    Countable (RingedSpace.moduleOpenHypercohomology X.toRingedSpace U
      ((DerivedTensor.Right.functor E).obj K.obj) i))

/- Lemma 36.33.2 (2): under the same affine-section countability hypothesis,
the degree-`i` Ext group from a perfect object restricted to a quasi-compact open
to the restriction of `K` is countable. -/
@[stacks 0CRP "(2)"] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.restrictedExtCountable :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (K : AlgebraicGeometry.Scheme.DerivedQCoh X)
    (hK : ∀ j : ℤ, ∀ V : X.affineOpens,
      Countable (RingedSpace.moduleSectionsOnOpen
        (RingedSpace.ModuleDerived.cohomologySheaf K.obj j) (V : X.Opens)))
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E) (U : X.Opens)
    (hU : IsCompact (U : Set X)) (i : ℤ),
    Countable
      (Ext⁽i⁾((RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace U).obj E,
        (RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace U).obj K.obj)))
