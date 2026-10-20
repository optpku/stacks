/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Over.FormallyLifting

/-!
# Smooth, étale, and unramified transformations are formally so

A representable transformation of functors on schemes over a base that is
smooth, étale, or unramified is respectively formally smooth, formally étale,
or formally unramified.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Over

namespace FormallySmooth

/-- A representable smooth transformation of functors on schemes over a base is
formally smooth. -/
theorem of_smooth {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (ha : (MorphismProperty.over (@Smooth)).presheaf a) :
    FormallySmooth a := sorry

/-- A representable smooth transformation is formally smooth when its smoothness
predicate is supplied as a fact. -/
instance instOfSmooth {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    {a : F ⟶ G} [Fact ((MorphismProperty.over (@Smooth)).presheaf a)] :
    FormallySmooth a := of_smooth a Fact.out

end FormallySmooth

namespace FormallyEtale

/-- A representable étale transformation of functors on schemes over a base is
formally étale. -/
theorem of_etale {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (ha : (MorphismProperty.over (@Etale)).presheaf a) :
    FormallyEtale a := sorry

/-- A representable étale transformation is formally étale when its étaleness
predicate is supplied as a fact. -/
instance instOfEtale {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    {a : F ⟶ G} [Fact ((MorphismProperty.over (@Etale)).presheaf a)] :
    FormallyEtale a := of_etale a Fact.out

end FormallyEtale

namespace FormallyUnramified

/-- A representable unramified transformation of functors on schemes over a base
is formally unramified. -/
theorem of_unramified {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (ha : (MorphismProperty.over (@Unramified)).presheaf a) :
    FormallyUnramified a := sorry

/-- A representable unramified transformation is formally unramified when its
unramifiedness predicate is supplied as a fact. -/
instance instOfUnramified {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    {a : F ⟶ G} [Fact ((MorphismProperty.over (@Unramified)).presheaf a)] :
    FormallyUnramified a := of_unramified a Fact.out

end FormallyUnramified

end AlgebraicGeometry.Scheme.Over
