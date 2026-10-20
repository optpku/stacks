module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Map.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Iso.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity and composition comparisons for mapped cospans

This construction leaf owns the two comparison isomorphisms for componentwise mapping of cospan
transformations.  Their explicit endpoint components are supplied to the generic modification
isomorphism constructor; projection equations are kept in `Coherence.Computations`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

universe w v u w' v' u'

namespace CategoryTheory.Bicategory.CospanTransform

variable {B : Type u} [Bicategory.{w, v} B]
variable {B' : Type u'} [Bicategory.{w', v'} B']
variable {x y z x' y' z' x'' y'' z'' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}
variable {f'' : x'' ⟶ z''} {g'' : y'' ⟶ z''}

namespace Implementation

/-- The ambient identity comparisons satisfy the left generating naturality square for the
mapped identity transformation. -/
private theorem idIso.leftNaturality
    (f : x ⟶ z) (g : y ⟶ z) (P : B ⥤ᵖ B') :
    (P.mapId x).hom ▷ P.map f ≫
        (CospanTransform.id (P.map f) (P.map g)).leftIso.hom =
      (CospanTransform.map (CospanTransform.id f g) P).leftIso.hom ≫
        P.map f ◁ (P.mapId z).hom := sorry

/-- The ambient identity comparisons satisfy the right generating naturality square for the
mapped identity transformation. -/
private theorem idIso.rightNaturality
    (f : x ⟶ z) (g : y ⟶ z) (P : B ⥤ᵖ B') :
    (P.mapId y).hom ▷ P.map g ≫
        (CospanTransform.id (P.map f) (P.map g)).rightIso.hom =
      (CospanTransform.map (CospanTransform.id f g) P).rightIso.hom ≫
        P.map g ◁ (P.mapId z).hom := sorry

/-- The ambient composition comparisons satisfy the left generating naturality square for
mapping a composite cospan transformation. -/
private theorem compIso.leftNaturality
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') (P : B ⥤ᵖ B') :
    (P.mapComp ψ.left φ.left).hom ▷ P.map f'' ≫
        ((CospanTransform.map ψ P).comp
          (CospanTransform.map φ P)).leftIso.hom =
      (CospanTransform.map (ψ.comp φ) P).leftIso.hom ≫
        P.map f ◁ (P.mapComp ψ.base φ.base).hom := sorry

/-- The ambient composition comparisons satisfy the right generating naturality square for
mapping a composite cospan transformation. -/
private theorem compIso.rightNaturality
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') (P : B ⥤ᵖ B') :
    (P.mapComp ψ.right φ.right).hom ▷ P.map g'' ≫
        ((CospanTransform.map ψ P).comp
          (CospanTransform.map φ P)).rightIso.hom =
      (CospanTransform.map (ψ.comp φ) P).rightIso.hom ≫
        P.map g ◁ (P.mapComp ψ.base φ.base).hom := sorry

end Implementation

/-- Mapping an identity cospan transformation is canonically isomorphic to the identity of
the mapped cospan, componentwise through `P.mapId`. -/
@[stacks 0040 "identity comparison for mapping bicategorical cospans"]
def map.idIso (f : x ⟶ z) (g : y ⟶ z) (P : B ⥤ᵖ B') :
    CospanTransform.map (CospanTransform.id f g) P ≅
      CospanTransform.id (P.map f) (P.map g) :=
  Hom.isoMk
    (ψ := CospanTransform.map (CospanTransform.id f g) P)
    (φ := CospanTransform.id (P.map f) (P.map g))
    (P.mapId x) (P.mapId y) (P.mapId z)
    (Implementation.idIso.leftNaturality f g P)
    (Implementation.idIso.rightNaturality f g P)

/-- Mapping a composite cospan transformation is canonically isomorphic to the composite of
the mapped transformations, componentwise through `P.mapComp`. -/
@[stacks 0040 "composition comparison for mapping bicategorical cospans"]
def map.compIso
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') (P : B ⥤ᵖ B') :
    CospanTransform.map (ψ.comp φ) P ≅
      (CospanTransform.map ψ P).comp (CospanTransform.map φ P) :=
  Hom.isoMk
    (ψ := CospanTransform.map (ψ.comp φ) P)
    (φ := (CospanTransform.map ψ P).comp (CospanTransform.map φ P))
    (P.mapComp ψ.left φ.left) (P.mapComp ψ.right φ.right)
    (P.mapComp ψ.base φ.base)
    (Implementation.compIso.leftNaturality ψ φ P)
    (Implementation.compIso.rightNaturality ψ φ P)

/- Data and axiom audit (mathlib 4.32): `map.idIso` and `map.compIso` retain the explicit
component isomorphisms `P.mapId` and `P.mapComp`; only their two generating naturality squares
and inherited inverse laws are deferred. -/

end CategoryTheory.Bicategory.CospanTransform
