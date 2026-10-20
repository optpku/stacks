/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.ChosenPresentation
import ReasLib.CategoryTheory.Sites.Sheaf.Monomorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite

universe u v

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y)

/- Definition 87.26.1: a morphism of formal algebraic spaces over a scheme is
monic exactly when each of its sheaf component maps is injective. -/
@[stacks 0AQB] #check (CategoryTheory.Sheaf.mono_iff_app_injective_type f :
  Mono f ↔ ∀ T : 𝒮.bigSite S, Function.Injective (f.hom.app (Opposite.op T)))

end AlgebraicGeometry.FormalAlgebraicSpace
