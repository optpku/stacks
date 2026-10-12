/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap96.«96_9_2_1_Comparison»
public import stacks_project.Chap96.«96_9_2_1_Restriction»

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u w

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable {x y : X.total} (φ : x ⟶ y) (F : Presheaf.{u + 1, u, w} X.total)

/- 96.9.2.1 Let `φ : x ⟶ y` be a morphism of a category fibred in groupoids `X`
over `(Sch/S)_fppf` lying over `a : U ⟶ V`, and let `F` be a presheaf on `X`.
The comparison morphism `c_φ` is the map of presheaves on `V_étale`
`restrictSmallEtale y F ⟶ (smallEtalePullback a).op ⋙ restrictSmallEtale x F`
whose component on an étale neighborhood `V' → V` is `F.map (op (comparisonPushHom φ V'))`,
where `U' = V' ×_V U` and `comparisonPushHom φ V'` is the unique lift in `X` of
the pullback square. -/
@[stacks 06W2]
#check (GroupoidsOver.comparisonPush φ F :
    GroupoidsOver.restrictSmallEtale y F ⟶
      (Scheme.smallEtalePullback (X.p.map φ).left).op ⋙
        GroupoidsOver.restrictSmallEtale x F)
