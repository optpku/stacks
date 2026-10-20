/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.DVRIndSmooth

@[expose] public section

/- Lemma 16.4.6 (tag 0BJ7): the map-first smooth-factorization criterion and
its weakly unramified DVR specialization are provided by ReasLib. -/

@[stacks 0BJ7]
#check @IsExtensionOfDiscreteValuationRings.WeaklyUnramified.indSmooth

@[stacks 0BJ7]
#check @IsExtensionOfDiscreteValuationRings.WeaklyUnramified.hasFactorisations

@[stacks 0BJ7]
#check @RingHom.IndSmooth.HasFactorisations.indSmooth
