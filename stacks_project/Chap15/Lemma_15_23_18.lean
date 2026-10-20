/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Reflexive.Normal
import StacksCheckRecall

/-!
# Lemma 15.23.18

@stack 0AVB

The normal-domain characterization of finite reflexive modules is owned by the reusable
reflexive-module API.
-/

@[expose] public section

/- The height-one localization intersection appearing in Lemma 15.23.18. -/
#check @Module.heightOneLocalizationIntersection

/- Lemma 15.23.18: over a Noetherian normal domain, a finite module is reflexive exactly when it
is torsion free and `(S₂)`, equivalently when it equals the intersection of its height-one
localizations inside the generic localization. -/
@[stacks 0AVB "Lemma 15.23.18"]
#check @Module.IsReflexive.normalDomain_tfae
