/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Approximation

/-!
# Lemma 15.103.5

@stack 0GYI
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ModuleCat

universe u

/- Lemma 15.103.5 (0GYI): for a ring map `A → B`, a derived base-change isomorphism admits
compatible enlargements of any pair of subcomplexes.  The reusable owner uses an explicit ring
homomorphism, exposes the comparison and induced maps, and packages the three source clauses in
the atomic `KernelControl`, `ImageControl`, and `CardinalBound` predicates. -/

@[stacks 0GYI "Lemma 15.103.5"]
#check fun {A B : Type u} [CommRing A] [CommRing B]
    (σ : A →+* B) ↦ ModuleCat.DerivedExtension.approximation σ

#check @ModuleCat.DerivedExtension.Approximation
#check @ModuleCat.DerivedExtension.mapCardinal
#check @ModuleCat.DerivedExtension.ApproximationAt
#check @ModuleCat.DerivedExtension.approximation_at
#check @ModuleCat.DerivedExtension.Cpx
#check @CochainComplex.totalCardinal
#check @ModuleCat.DerivedExtension.pairCardinal

/- The concrete maps are public ReasLib data, so downstream statements can use them without
reconstructing an adjunction or a factor-through morphism. -/
#check @ModuleCat.DerivedExtension.restrictionComplex
#check @ModuleCat.DerivedExtension.comparison
#check @ModuleCat.DerivedExtension.restrict
#check @ModuleCat.DerivedExtension.homologyMap
#check @ModuleCat.DerivedExtension.sourceMap
#check @ModuleCat.DerivedExtension.targetMap
#check @ModuleCat.DerivedExtension.Enlargement
#check @ModuleCat.DerivedExtension.KernelControl
#check @ModuleCat.DerivedExtension.ImageControl
#check @ModuleCat.DerivedExtension.CardinalBound
#check @ModuleCat.DerivedExtension.Controls
