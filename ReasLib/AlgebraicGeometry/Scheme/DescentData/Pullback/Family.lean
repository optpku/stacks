/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Family
public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Coproduct

/-!
# Pullback of scheme descent data along a morphism of families

This module specializes pseudofunctorial pullback of descent data to fixed-target families of
schemes and compares it with pullback along the induced morphism of coproducts.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Scheme.DescentData.Pullback

variable {S S' : Scheme.{u}}
variable {𝒰 : SemiRepresentableFamily.Over.{v} S'}
variable {𝒱 : SemiRepresentableFamily.Over.{w} S}
variable {base : S' ⟶ S}

/-- Pullback of scheme descent data along a morphism of fixed-target families. -/
noncomputable abbrev functorOfHom
    (φ : SemiRepresentableFamily.Over.Hom
      (SemiRepresentableFamily.Over.map (Over.map base) 𝒰) 𝒱) :
    DescentData (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom) ⥤
      DescentData (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom) :=
  Pseudofunctor.DescentData.pullFunctor Scheme.overPseudofunctor
    (SemiRepresentableFamily.Over.Hom.map_hom base φ)

/-- The component at `i` of a pulled-back scheme descent datum is pullback along the component
map of the family morphism. -/
theorem functorOfHom_obj_obj
    (φ : SemiRepresentableFamily.Over.Hom
      (SemiRepresentableFamily.Over.map (Over.map base) 𝒰) 𝒱)
    (D : DescentData (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom))
    (i : 𝒰.index) :
    ((functorOfHom φ).obj D).obj i =
      (Over.pullback (φ.f i).left).obj (D.obj (φ.α i)) := sorry

/-- The transition map of a pulled-back scheme descent datum is the canonical
pseudofunctorial pullback of the original transition map. -/
theorem functorOfHom_obj_hom
    (φ : SemiRepresentableFamily.Over.Hom
      (SemiRepresentableFamily.Over.map (Over.map base) 𝒰) 𝒱)
    (D : DescentData (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom))
    {Y : Scheme.{u}} (q : Y ⟶ S') {i i' : 𝒰.index}
    (f : Y ⟶ (𝒰.obj i).left) (f' : Y ⟶ (𝒰.obj i').left)
    (hf : f ≫ (𝒰.obj i).hom = q) (hf' : f' ≫ (𝒰.obj i').hom = q) :
    ((functorOfHom φ).obj D).hom q f f' hf hf' =
      Pseudofunctor.DescentData.pullFunctorObjHom
        (F := Scheme.overPseudofunctor)
        (f := fun j : 𝒱.index ↦ (𝒱.obj j).hom) (p := base)
        (f' := fun j : 𝒰.index ↦ (𝒰.obj j).hom) (α := φ.α)
        (p' := fun j ↦ (φ.f j).left)
        (w := SemiRepresentableFamily.Over.Hom.map_hom base φ)
        D q f f' hf hf' := sorry

/-- Pullback of a morphism of scheme descent data acts componentwise by pullback along the
corresponding component of the family morphism. -/
theorem functorOfHom_map_hom
    (φ : SemiRepresentableFamily.Over.Hom
      (SemiRepresentableFamily.Over.map (Over.map base) 𝒰) 𝒱)
    {D E : DescentData (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom)}
    (η : D ⟶ E) (i : 𝒰.index) :
    ((functorOfHom φ).map η).hom i =
      (Over.pullback (φ.f i).left).map (η.hom (φ.α i)) := sorry

/-- Two morphisms of fixed-target scheme families over the same base map induce canonically
isomorphic pullback functors on scheme descent data. -/
noncomputable def isoOfHom
    (φ φ' : SemiRepresentableFamily.Over.Hom
      (SemiRepresentableFamily.Over.map (Over.map base) 𝒰) 𝒱) :
    functorOfHom φ ≅ functorOfHom φ' :=
  Pseudofunctor.DescentData.pullFunctorIso
    (F := Scheme.overPseudofunctor)
    (f := fun j : 𝒱.index ↦ (𝒱.obj j).hom) (p := base)
    (f' := fun i : 𝒰.index ↦ (𝒰.obj i).hom)
    (α := φ.α) (p' := fun i ↦ (φ.f i).left)
    (w := SemiRepresentableFamily.Over.Hom.map_hom base φ)
    (β := φ'.α) (p'' := fun i ↦ (φ'.f i).left)
    (SemiRepresentableFamily.Over.Hom.map_hom base φ')

/-- The forward same-base comparison at `i` is the comparison furnished by the original
descent datum between the two chosen component maps. -/
theorem isoOfHom_hom_app_hom
    (φ φ' : SemiRepresentableFamily.Over.Hom
      (SemiRepresentableFamily.Over.map (Over.map base) 𝒰) 𝒱)
    (D : DescentData (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom))
    (i : 𝒰.index) :
    ((isoOfHom φ φ').hom.app D).hom i =
      D.hom ((𝒰.obj i).hom ≫ base) (φ.f i).left (φ'.f i).left
        (SemiRepresentableFamily.Over.Hom.map_hom base φ i)
        (SemiRepresentableFamily.Over.Hom.map_hom base φ' i) := sorry

/-- The morphism between coproducts induced by a morphism of fixed-target scheme families. -/
noncomputable def coproductMapOfHom [Small.{u} 𝒰.index] [Small.{u} 𝒱.index]
    (φ : SemiRepresentableFamily.Over.Hom
      (SemiRepresentableFamily.Over.map (Over.map base) 𝒰) 𝒱) :
    (∐ fun i ↦ (𝒰.obj i).left) ⟶ ∐ fun j ↦ (𝒱.obj j).left :=
  Sigma.desc fun i ↦ (φ.f i).left ≫ Sigma.ι (fun j ↦ (𝒱.obj j).left) (φ.α i)

/-- The induced coproduct map restricts on the `i`-th coproduct summand to the corresponding
component map followed by the target coproduct injection. -/
theorem coproductMapOfHom_ι [Small.{u} 𝒰.index] [Small.{u} 𝒱.index]
    (φ : SemiRepresentableFamily.Over.Hom
      (SemiRepresentableFamily.Over.map (Over.map base) 𝒰) 𝒱) (i : 𝒰.index) :
    Sigma.ι (fun i ↦ (𝒰.obj i).left) i ≫ coproductMapOfHom φ =
      (φ.f i).left ≫ Sigma.ι (fun j ↦ (𝒱.obj j).left) (φ.α i) := sorry

/-- The induced coproduct map and `base` form a commutative square with the two coproduct
arrows. -/
theorem coproductMapOfHom_fac [Small.{u} 𝒰.index] [Small.{u} 𝒱.index]
    (φ : SemiRepresentableFamily.Over.Hom
      (SemiRepresentableFamily.Over.map (Over.map base) 𝒰) 𝒱) :
    coproductMapOfHom φ ≫
        Scheme.DescentData.coproductArrow
          (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom) PUnit.unit =
      Scheme.DescentData.coproductArrow
          (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom) PUnit.unit ≫ base := sorry

/-- Pullback through a source coproduct injection and then through the induced coproduct map
lies over `base`. -/
theorem coproductMapOfHom_left_fac [Small.{u} 𝒰.index] [Small.{u} 𝒱.index]
    (φ : SemiRepresentableFamily.Over.Hom
      (SemiRepresentableFamily.Over.map (Over.map base) 𝒰) 𝒱) (i : 𝒰.index) :
    (Sigma.ι (fun k ↦ (𝒰.obj k).left) i ≫ coproductMapOfHom φ) ≫
        Scheme.DescentData.coproductArrow
          (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom) PUnit.unit =
      (𝒰.obj i).hom ≫ base := sorry

/-- Pullback through a component map and its target coproduct injection lies over `base`. -/
theorem coproductMapOfHom_right_fac [Small.{u} 𝒰.index] [Small.{u} 𝒱.index]
    (φ : SemiRepresentableFamily.Over.Hom
      (SemiRepresentableFamily.Over.map (Over.map base) 𝒰) 𝒱) (i : 𝒰.index) :
    ((φ.f i).left ≫ Sigma.ι (fun k ↦ (𝒱.obj k).left) (φ.α i)) ≫
        Scheme.DescentData.coproductArrow
          (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom) PUnit.unit =
      (𝒰.obj i).hom ≫ base := sorry

/-- Pulling back from the target coproduct first through the induced coproduct map and then
through the source coproduct injections is compatible with componentwise family pullback. -/
noncomputable def coproductRestrictionIsoOfHom
    [Small.{u} 𝒰.index] [Small.{u} 𝒱.index]
    (φ : SemiRepresentableFamily.Over.Hom
      (SemiRepresentableFamily.Over.map (Over.map base) 𝒰) 𝒱) :
    Pullback.functor
          (Scheme.DescentData.coproductArrow
            (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom) PUnit.unit)
          (Scheme.DescentData.coproductArrow
            (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom) PUnit.unit)
          base (coproductMapOfHom φ) (CommSq.mk (coproductMapOfHom_fac φ)) ⋙
        Scheme.DescentData.restrictCoproduct
          (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom) ≅
      Scheme.DescentData.restrictCoproduct
          (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom) ⋙
        functorOfHom φ :=
  Pseudofunctor.DescentData.pullFunctorCompIso
      (F := Scheme.overPseudofunctor)
      (f := fun _ : PUnit.{1} ↦ Scheme.DescentData.coproductArrow
        (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom) PUnit.unit)
      (p := base)
      (f' := fun _ : PUnit.{1} ↦ Scheme.DescentData.coproductArrow
        (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom) PUnit.unit)
      (α := fun _ ↦ PUnit.unit) (p' := fun _ ↦ coproductMapOfHom φ)
      (w := fun _ ↦ coproductMapOfHom_fac φ)
      (q := 𝟙 S') (f'' := fun i : 𝒰.index ↦ (𝒰.obj i).hom)
      (β := fun _ ↦ PUnit.unit)
      (q' := fun i ↦ Sigma.ι (fun k ↦ (𝒰.obj k).left) i)
      (w' := Scheme.DescentData.coproductInjection_fac
        (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom))
      base ≪≫
    Pseudofunctor.DescentData.pullFunctorIso Scheme.overPseudofunctor
      (coproductMapOfHom_left_fac φ) (coproductMapOfHom_right_fac φ) ≪≫
    (Pseudofunctor.DescentData.pullFunctorCompIso
      (F := Scheme.overPseudofunctor)
      (f := fun _ : PUnit.{1} ↦ Scheme.DescentData.coproductArrow
        (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom) PUnit.unit)
      (p := 𝟙 S) (f' := fun j : 𝒱.index ↦ (𝒱.obj j).hom)
      (α := fun _ ↦ PUnit.unit)
      (p' := fun j ↦ Sigma.ι (fun k ↦ (𝒱.obj k).left) j)
      (w := Scheme.DescentData.coproductInjection_fac
        (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom))
      (q := base) (f'' := fun i : 𝒰.index ↦ (𝒰.obj i).hom)
      (β := φ.α) (q' := fun i ↦ (φ.f i).left)
      (w' := SemiRepresentableFamily.Over.Hom.map_hom base φ)
      base).symm

/-- After restricting to the source-family components, the coproduct comparison is the
canonical comparison built from pseudofunctorial composition. -/
noncomputable def coproductComparisonAfterRestrictionOfHom
    [Small.{u} 𝒰.index] [Small.{u} 𝒱.index]
    (φ : SemiRepresentableFamily.Over.Hom
      (SemiRepresentableFamily.Over.map (Over.map base) 𝒰) 𝒱) :
    ((Scheme.DescentData.coproductEquivalence
          (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom)).functor ⋙
        Pullback.functor
          (Scheme.DescentData.coproductArrow
            (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom) PUnit.unit)
          (Scheme.DescentData.coproductArrow
            (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom) PUnit.unit)
          base (coproductMapOfHom φ) (CommSq.mk (coproductMapOfHom_fac φ))) ⋙
        Scheme.DescentData.restrictCoproduct
          (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom) ≅
      (functorOfHom φ ⋙
        (Scheme.DescentData.coproductEquivalence
          (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom)).functor) ⋙
        Scheme.DescentData.restrictCoproduct
          (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (coproductRestrictionIsoOfHom φ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Scheme.DescentData.coproductUnitIso
        (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom)).symm _ ≪≫
    Functor.leftUnitor _ ≪≫
    (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _
      (Scheme.DescentData.coproductUnitIso
        (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom)) ≪≫
    (Functor.associator _ _ _).symm

/-- Under the coproduct equivalences, family pullback is canonically isomorphic to pullback
along the induced commutative square of coproduct morphisms. -/
noncomputable def coproductIsoOfHom [Small.{u} 𝒰.index] [Small.{u} 𝒱.index]
    (φ : SemiRepresentableFamily.Over.Hom
      (SemiRepresentableFamily.Over.map (Over.map base) 𝒰) 𝒱) :
    (Scheme.DescentData.coproductEquivalence
        (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom)).functor ⋙
      Pullback.functor
        (Scheme.DescentData.coproductArrow
          (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom) PUnit.unit)
        (Scheme.DescentData.coproductArrow
          (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom) PUnit.unit)
        base (coproductMapOfHom φ) (CommSq.mk (coproductMapOfHom_fac φ)) ≅
      functorOfHom φ ⋙
        (Scheme.DescentData.coproductEquivalence
          (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom)).functor :=
  Functor.fullyFaithfulCancelRight
    (Scheme.DescentData.restrictCoproduct
      (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom))
    (coproductComparisonAfterRestrictionOfHom φ)

/-- Restriction along the source coproduct injections identifies each component of the
coproduct comparison with its canonical pseudofunctorial construction. -/
theorem coproductIsoOfHom_hom_app [Small.{u} 𝒰.index] [Small.{u} 𝒱.index]
    (φ : SemiRepresentableFamily.Over.Hom
      (SemiRepresentableFamily.Over.map (Over.map base) 𝒰) 𝒱)
    (D : DescentData (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom)) :
    (Scheme.DescentData.restrictCoproduct
      (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom)).map
        ((coproductIsoOfHom φ).hom.app D) =
      (coproductComparisonAfterRestrictionOfHom φ).hom.app D := sorry

end AlgebraicGeometry.Scheme.DescentData.Pullback
