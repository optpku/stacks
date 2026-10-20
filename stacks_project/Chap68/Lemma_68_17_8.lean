/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DescentConditions
import StacksCheckRecall

/-!
# Descent of property (β), decent, and reasonable algebraic spaces

If `f : X ⟶ Y` is a quasi-compact étale surjective morphism of algebraic spaces
and `X` has property (ω), for `ω` among property (β), decent, and reasonable, then
`Y` has (ω).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.17.8 (1): If `f : X ⟶ Y` is a quasi-compact étale surjective morphism of
algebraic spaces and `X` has property (β), then `Y` has property (β). -/
@[stacks 03L2] #check (AlgebraicGeometry.AlgebraicSpace.hasPropertyBeta_inheritedFromSource :
  ∀ {S : Scheme.{u}},
    InheritedFromSource (@HasPropertyBeta S : ObjectProperty (AlgebraicSpace S))
      ((@QuasiCompact S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Etale S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Surjective S : MorphismProperty (AlgebraicSpace S))))

/- Lemma 68.17.8 (2): If `f : X ⟶ Y` is a quasi-compact étale surjective morphism of
algebraic spaces and `X` is decent, then `Y` is decent. -/
@[stacks 03L2] #check (AlgebraicGeometry.AlgebraicSpace.isDecent_inheritedFromSource :
  ∀ {S : Scheme.{u}},
    InheritedFromSource (@IsDecent S : ObjectProperty (AlgebraicSpace S))
      ((@QuasiCompact S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Etale S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Surjective S : MorphismProperty (AlgebraicSpace S))))

/- Lemma 68.17.8 (3): If `f : X ⟶ Y` is a quasi-compact étale surjective morphism of
algebraic spaces and `X` is reasonable, then `Y` is reasonable. -/
@[stacks 03L2] #check (AlgebraicGeometry.AlgebraicSpace.isReasonable_inheritedFromSource :
  ∀ {S : Scheme.{u}},
    InheritedFromSource (@IsReasonable S : ObjectProperty (AlgebraicSpace S))
      ((@QuasiCompact S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Etale S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Surjective S : MorphismProperty (AlgebraicSpace S))))

/- If `f : X ⟶ Y` is quasi-compact, étale, and surjective, and `X` has property
(β), then `Y` has property (β). -/
#check (AlgebraicGeometry.AlgebraicSpace.HasPropertyBeta.of_quasiCompact_etale_surjective :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [QuasiCompact f] → [Etale f] → [Surjective f] → [HasPropertyBeta X] → HasPropertyBeta Y)

/- If `f : X ⟶ Y` is quasi-compact, étale, and surjective, and `X` is decent, then
`Y` is decent. -/
#check (AlgebraicGeometry.AlgebraicSpace.IsDecent.of_quasiCompact_etale_surjective :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [QuasiCompact f] → [Etale f] → [Surjective f] → [IsDecent X] → IsDecent Y)

/- If `f : X ⟶ Y` is quasi-compact, étale, and surjective, and `X` is reasonable,
then `Y` is reasonable. -/
#check (AlgebraicGeometry.AlgebraicSpace.IsReasonable.of_quasiCompact_etale_surjective :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [QuasiCompact f] → [Etale f] → [Surjective f] → [IsReasonable X] → IsReasonable Y)

end AlgebraicGeometry.AlgebraicSpace
