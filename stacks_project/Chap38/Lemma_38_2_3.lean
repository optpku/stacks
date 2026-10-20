/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Etale
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 38.2.3 (1): relative flatness of a quasi-coherent module at a point is
unchanged after composing the base morphism with an étale morphism. -/
@[stacks 05B9]
#check (AlgebraicGeometry.Scheme.Modules.flatOverAt_comp_iff_of_etale :
  ∀ {X T S : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ S) (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [Etale g] (x : X),
    flatOverAt ℱ (f ≫ g) x ↔ flatOverAt ℱ f x)

/- Lemma 38.2.3 (2): global relative flatness of a quasi-coherent module is
unchanged after composing the base morphism with an étale morphism. -/
@[stacks 05B9]
#check (AlgebraicGeometry.Scheme.Modules.flatOver_comp_iff_of_etale :
  ∀ {X T S : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ S) (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [Etale g],
    flatOver ℱ (f ≫ g) ↔ flatOver ℱ f)

end AlgebraicGeometry.Scheme.Modules
