/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal

/-!
# Stored structures on complete local algebras

This opt-in leaf makes the structures already carried by a complete local algebra
available to typeclass inference, without changing the carrier or algebra map.
-/

@[expose] public section

attribute [instance] CompleteLocalAlgCat.algebra CompleteLocalAlgCat.isLocalRing
  CompleteLocalAlgCat.isNoetherianRing CompleteLocalAlgCat.isCompleteLocalRing
  CompleteLocalAlgCat.Hom.isLocalHom
