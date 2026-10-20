/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Locus.Noetherian
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Theorem 41.10.1 (1): For a locally finite type morphism to a locally Noetherian
scheme, the locus where a coherent module is flat over the target is open. -/
@[stacks 0255] #check
  (AlgebraicGeometry.Scheme.Modules.isOpen_flatOverAt_of_locallyNoetherian :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y]
      [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent],
      IsOpen {x : X | Scheme.Modules.flatOverAt F f x})

/- Theorem 41.10.1 (2): For a locally finite type morphism to a locally Noetherian
scheme, the locus where the morphism is flat is open. -/
@[stacks 0255] #check
  (AlgebraicGeometry.Scheme.Hom.isOpen_flatAt_of_locallyNoetherian :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y]
      [LocallyOfFiniteType f],
      IsOpen {x : X | Scheme.Hom.flatAt f x})
