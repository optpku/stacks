/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.DerivedPushforwardComparison
import StacksCheckRecall

/-!
With the assumptions and notation of Lemma 103.15.1, the canonical base-change
map `g⁻¹ Rf_* F ⟶ Rf'_*(g')⁻¹ F` is an isomorphism for every abelian sheaf `F`
on `X_étale` (resp. `X_fppf`).
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidsOver CategoryTheory
open scoped Bicategory

universe u z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]
variable [UnivLE.{u + 1, z}]
variable (f : X ⟶ Y)

section Smooth

variable [Smooth f]

/- Lemma 103.15.3 (1): with the assumptions and notation of Lemma 103.15.1,
the canonical base-change map `g⁻¹ Rf_* F ⟶ Rf'_*(g')⁻¹ F` is an isomorphism
for every abelian sheaf `F` on `X_étale`. The derived natural transformation
includes every such sheaf concentrated in degree zero. -/
@[stacks 0GR3] #check
  (AlgebraicGeometry.AlgebraicStack.lisseEtaleAbelianDerivedPushforwardRestrictionComparison.instIsIso.{u, z} f :
    IsIso (AlgebraicGeometry.AlgebraicStack.lisseEtaleAbelianDerivedPushforwardRestrictionComparison.{u, z} f))

end Smooth

section Flat

variable [Flat f]

/- Lemma 103.15.3 (2): with the assumptions and notation of Lemma 103.15.1,
the canonical base-change map `g⁻¹ Rf_* F ⟶ Rf'_*(g')⁻¹ F` is an isomorphism
for every abelian sheaf `F` on `X_fppf`. The derived natural transformation
includes every such sheaf concentrated in degree zero. -/
@[stacks 0GR3] #check
  (AlgebraicGeometry.AlgebraicStack.flatFppfAbelianDerivedPushforwardRestrictionComparison.instIsIso.{u, z} f :
    IsIso (AlgebraicGeometry.AlgebraicStack.flatFppfAbelianDerivedPushforwardRestrictionComparison.{u, z} f))

end Flat

end AlgebraicGeometry.AlgebraicStack
