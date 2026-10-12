/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Over.FormallySmooth.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Over.FormallyEtale.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Over.FormallyUnramified.Composition
import StacksCheckRecall

/-!
# Composition of formally smooth, étale, and unramified transformations

A composition of formally smooth (resp. formally étale, formally unramified)
transformations of functors is again formally smooth (resp. formally étale,
formally unramified).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Over

/- Lemma 76.13.3 (1): A composition of formally smooth transformations of
functors is formally smooth. -/
@[stacks 049T]
#check (AlgebraicGeometry.Scheme.Over.FormallySmooth.comp :
  ∀ {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H)
    [FormallySmooth a] [FormallySmooth b], FormallySmooth (a ≫ b))

/- Lemma 76.13.3 (2): A composition of formally étale transformations of
functors is formally étale. -/
@[stacks 049T]
#check (AlgebraicGeometry.Scheme.Over.FormallyEtale.comp :
  ∀ {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H)
    [FormallyEtale a] [FormallyEtale b], FormallyEtale (a ≫ b))

/- Lemma 76.13.3 (3): A composition of formally unramified transformations of
functors is formally unramified. -/
@[stacks 049T]
#check (AlgebraicGeometry.Scheme.Over.FormallyUnramified.comp :
  ∀ {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H)
    [FormallyUnramified a] [FormallyUnramified b], FormallyUnramified (a ≫ b))

end AlgebraicGeometry.Scheme.Over
