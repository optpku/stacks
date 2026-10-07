module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow
import Mathlib.Tactic.CrossRefAttribute

/-!
# Squares of bounded-below right-derived functors

An underived natural transformation `F ⋙ G ⟶ I ⋙ H` induces a transformation
`RF ⋙ RG ⟶ RI ⋙ RH` whenever the source composition comparison is invertible.  Keeping the
generic square independent of geometry lets base-change constructions reuse one canonical owner.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB wC wD vA vB vC vD uA uB uC uD

namespace CategoryTheory.Functor.RightDerived.Composition.BoundedBelow.Square

set_option maxHeartbeats 800000

variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
  [Category.{vA} A] [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

variable {F : A ⥤ B} {G : B ⥤ C} {I : A ⥤ D} {H : D ⥤ C}
  [F.Additive] [G.Additive] [I.Additive] [H.Additive]

variable [F.toBoundedBelowDerived.HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso A)]
variable [G.toBoundedBelowDerived.HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso B)]
variable [I.toBoundedBelowDerived.HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso A)]
variable [H.toBoundedBelowDerived.HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso D)]
variable [(F ⋙ G).toBoundedBelowDerived.HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso A)]
variable [(I ⋙ H).toBoundedBelowDerived.HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso A)]

/-- The two-stage source of a bounded-below right-derived square. -/
@[stacks 015M "bounded-below right-derived square source"]
abbrev source (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso B)] :
    DerivedCategory.Plus A ⥤ DerivedCategory.Plus C :=
  Functor.RightDerived.Bounded.functor F ⋙ Functor.RightDerived.Bounded.functor G

/-- The two-stage target of a bounded-below right-derived square. -/
@[stacks 015M "bounded-below right-derived square target"]
abbrev target (I : A ⥤ D) (H : D ⥤ C) [I.Additive] [H.Additive]
    [I.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [H.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso D)] :
    DerivedCategory.Plus A ⥤ DerivedCategory.Plus C :=
  Functor.RightDerived.Bounded.functor I ⋙ Functor.RightDerived.Bounded.functor H

/-- The bounded-below right-derived square map built from an explicit identification of the
one-stage source with the two-stage source.  This is the data-clean entry point for clients that
own a concrete comparison isomorphism. -/
@[stacks 015M "bounded-below right-derived square map from a source isomorphism"]
noncomputable def mapOfIso
    (τ : F ⋙ G ⟶ I ⋙ H)
    (e : Functor.RightDerived.Bounded.functor (F ⋙ G) ≅ source F G) :
    source F G ⟶ target I H :=
  e.inv ≫ Functor.RightDerived.Bounded.map τ ≫
    Functor.RightDerived.Composition.BoundedBelow.comparison I H

/-- The canonical bounded-below right-derived map attached to an underived square. -/
@[stacks 015M "bounded-below right-derived square map"]
noncomputable def map
    (τ : F ⋙ G ⟶ I ⋙ H)
    (h : IsIso (Functor.RightDerived.Composition.BoundedBelow.comparison F G)) :
    source F G ⟶ target I H :=
  mapOfIso τ
    (@asIso _ _ _ _
      (Functor.RightDerived.Composition.BoundedBelow.comparison F G) h)

/-- Specification of a square map constructed from an explicit source comparison
isomorphism. -/
@[stacks 015M "bounded-below right-derived square specification from a source isomorphism"]
def IsMapOfIso
    (τ : F ⋙ G ⟶ I ⋙ H)
    (e : Functor.RightDerived.Bounded.functor (F ⋙ G) ≅ source F G)
    (η : source F G ⟶ target I H) : Prop :=
  e.hom ≫ η = Functor.RightDerived.Bounded.map τ ≫
    Functor.RightDerived.Composition.BoundedBelow.comparison I H

/-- A natural transformation is the bounded-below right-derived map of `τ` when it satisfies
the canonical comparison equation. -/
@[stacks 015M "bounded-below right-derived square specification"]
def IsMap (τ : F ⋙ G ⟶ I ⋙ H)
    (η : source F G ⟶ target I H) : Prop :=
  Functor.RightDerived.Composition.BoundedBelow.comparison F G ≫ η =
    Functor.RightDerived.Bounded.map τ ≫
      Functor.RightDerived.Composition.BoundedBelow.comparison I H

/-- Objectwise form of the bounded-below right-derived square specification. -/
@[stacks 015M "bounded-below right-derived square component specification"]
def IsMapAt (τ : F ⋙ G ⟶ I ⋙ H) (K : DerivedCategory.Plus A)
    (η : (source F G).obj K ⟶ (target I H).obj K) : Prop :=
  (Functor.RightDerived.Composition.BoundedBelow.comparison F G).app K ≫ η =
    (Functor.RightDerived.Bounded.map τ).app K ≫
      (Functor.RightDerived.Composition.BoundedBelow.comparison I H).app K

/-- The map built from an explicit source comparison isomorphism satisfies its defining
equation. -/
@[stacks 015M "bounded-below right-derived square map-from-iso specification"]
theorem mapOfIso_isMapOfIso
    (τ : F ⋙ G ⟶ I ⋙ H)
    (e : Functor.RightDerived.Bounded.functor (F ⋙ G) ≅ source F G) :
    IsMapOfIso τ e (mapOfIso τ e) := sorry

/-- The explicit-source-iso specification determines the square map uniquely. -/
@[stacks 015M "uniqueness of bounded-below square maps from a source isomorphism"]
theorem IsMapOfIso.eq_mapOfIso
    (τ : F ⋙ G ⟶ I ⋙ H)
    (e : Functor.RightDerived.Bounded.functor (F ⋙ G) ≅ source F G)
    {η : source F G ⟶ target I H}
    (hη : IsMapOfIso τ e η) :
    η = mapOfIso τ e := sorry

/-- The canonical map satisfies the right-derived square specification. -/
@[stacks 015M "bounded-below right-derived square map specification"]
theorem map_isMap
    (τ : F ⋙ G ⟶ I ⋙ H)
    (h : IsIso (Functor.RightDerived.Composition.BoundedBelow.comparison F G)) :
    IsMap τ (map τ h) := sorry

/-- If the underived square map and the target composition comparison are invertible, then the
bounded-below square map built from a concrete source isomorphism is invertible. -/
@[stacks 015M "bounded-below right-derived square isomorphism transport"]
theorem mapOfIso_isIso
    (τ : F ⋙ G ⟶ I ⋙ H)
    (e : Functor.RightDerived.Bounded.functor (F ⋙ G) ≅ source F G)
    [IsIso τ]
    [IsIso (Functor.RightDerived.Composition.BoundedBelow.comparison I H)] :
    IsIso (mapOfIso τ e) := sorry

/-- If the underived square map and the target composition comparison are invertible, then the
canonical bounded-below square map is invertible. -/
@[stacks 015M "bounded-below right-derived square isomorphism transport"]
theorem map_isIso
    (τ : F ⋙ G ⟶ I ⋙ H)
    (h : IsIso (Functor.RightDerived.Composition.BoundedBelow.comparison F G))
    [IsIso τ]
    [IsIso (Functor.RightDerived.Composition.BoundedBelow.comparison I H)] :
    IsIso (map τ h) := sorry

/-- Every component of the canonical map satisfies the objectwise specification. -/
@[stacks 015M "bounded-below right-derived square component specification"]
theorem map_isMapAt
    (τ : F ⋙ G ⟶ I ⋙ H)
    (h : IsIso (Functor.RightDerived.Composition.BoundedBelow.comparison F G))
    (K : DerivedCategory.Plus A) :
    IsMapAt τ K ((map τ h).app K) := sorry

/-- A natural transformation satisfying the comparison equation is the canonical square map. -/
@[stacks 015M "uniqueness of bounded-below right-derived square maps"]
theorem IsMap.eq_map
    (τ : F ⋙ G ⟶ I ⋙ H)
    (h : IsIso (Functor.RightDerived.Composition.BoundedBelow.comparison F G))
    {η : source F G ⟶ target I H}
    (hη : IsMap τ η) :
    η = map τ h := sorry

/-- A component satisfying the comparison equation is the component of the canonical square
map. -/
@[stacks 015M "uniqueness of bounded-below right-derived square components"]
theorem IsMapAt.eq_map
    (τ : F ⋙ G ⟶ I ⋙ H)
    (h : IsIso (Functor.RightDerived.Composition.BoundedBelow.comparison F G))
    (K : DerivedCategory.Plus A)
    {η : (source F G).obj K ⟶ (target I H).obj K}
    (hη : IsMapAt τ K η) :
    η = (map τ h).app K := sorry

end CategoryTheory.Functor.RightDerived.Composition.BoundedBelow.Square
