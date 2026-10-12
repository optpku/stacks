/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Over.RepresentableLifting
import StacksCheckRecall

/-!
# Representable smooth, étale, and unramified transformations are formally so

A representable transformation of functors on `(Sch/S)_fppf` that is smooth,
étale, or unramified is respectively formally smooth, formally étale, or
formally unramified.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Over

universe u

/- Lemma 76.13.5 (1): A representable transformation of functors on
`(Sch/S)_fppf` that is smooth is formally smooth. -/
@[stacks 04AL]
#check (AlgebraicGeometry.Scheme.Over.FormallySmooth.of_smooth :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G),
      (MorphismProperty.over (@Smooth)).presheaf a → FormallySmooth a)

/- Lemma 76.13.5 (2): A representable transformation of functors on
`(Sch/S)_fppf` that is étale is formally étale. -/
@[stacks 04AL]
#check (AlgebraicGeometry.Scheme.Over.FormallyEtale.of_etale :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G),
      (MorphismProperty.over (@Etale)).presheaf a → FormallyEtale a)

/- Lemma 76.13.5 (3): A representable transformation of functors on
`(Sch/S)_fppf` that is unramified is formally unramified. -/
@[stacks 04AL]
#check (AlgebraicGeometry.Scheme.Over.FormallyUnramified.of_unramified :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G),
      (MorphismProperty.over (@Unramified)).presheaf a → FormallyUnramified a)
