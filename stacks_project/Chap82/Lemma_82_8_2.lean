/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.ProperPushforward
import StacksCheckRecall

/-!
# Functoriality of proper pushforward of cycles

In Situation 82.2.1, successive proper pushforwards of `k`-cycles along
morphisms of good algebraic spaces over `B` agree with pushforward along the
composite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/- Lemma 82.8.2: In Situation 82.2.1 let `X`, `Y`, `Z / B` be good. Let
`f : X ⟶ Y` and `g : Y ⟶ Z` be proper morphisms over `B`. Then
`g_* ∘ f_* = (g ∘ f)_*` as maps `Z_k(X) → Z_k(Z)`. -/
@[stacks 0EP2] #check (AlgebraicGeometry.AlgebraicSpace.Hom.properPushforward_comp :
  ∀ {S : Scheme.{u}} {B X Y Z : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pZ : Z ⟶ B) [QuasiSeparated pZ] [LocallyOfFiniteType pZ]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) [Proper f] (g : Y ⟶ Z) [Proper g]
    (hf : f ≫ pY = pX) (hg : g ≫ pZ = pY) (k : ℤ),
    (properPushforwardHom pY pZ δ g hg k).comp
        (properPushforwardHom pX pY δ f hf k) =
      properPushforwardHom pX pZ δ (f ≫ g) (by rw [Category.assoc, hg, hf])
        k)

end Hom

end AlgebraicGeometry.AlgebraicSpace
