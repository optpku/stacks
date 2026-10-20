/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.Existence
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Compactification

/- Lemma 38.32.2: if `X` is compactifiable over a quasi-compact quasi-separated scheme `S`,
then an `S`-morphism `f : X ⟶ Y` to a separated finite type scheme makes `X` compactifiable
over `Y`. -/
@[stacks 0A9Z]
#check (AlgebraicGeometry.Scheme.Compactification.Of.nonempty_over :
  ∀ {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    {X Y : Over S} (f : X ⟶ Y) [IsSeparated Y.hom] [Scheme.Hom.FiniteType Y.hom]
    [Nonempty (Of S X)], Nonempty (Of Y.left (Over.mk f.left)))

end AlgebraicGeometry.Scheme.Compactification
