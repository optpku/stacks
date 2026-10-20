/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Noetherian
import ReasLib.RingTheory.Normal.Nagata.EssentialFiniteness

@[expose] public section

/-!
# Nagata properties under locally finite type morphisms

Universal Japaneseness and the Nagata property pass from the target of a
locally finite type morphism of schemes to its source.
-/

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme locally of finite type over a universally Japanese scheme is universally Japanese. -/
theorem universallyJapanese_of_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [UniversallyJapanese S] :
    UniversallyJapanese X := sorry

/-- A scheme locally of finite type over a Nagata scheme is Nagata. -/
theorem nagata_of_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [Nagata S] :
    Nagata X := sorry

end AlgebraicGeometry.Scheme
