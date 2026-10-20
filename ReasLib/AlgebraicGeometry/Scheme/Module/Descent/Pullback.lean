/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Descent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.Quasicoherent

/-!
# Pullback of quasi-coherent descent data along morphisms of scheme families

A morphism between fixed-target families of schemes induces pullback on quasi-coherent
descent data. Morphisms of families over the same base map induce canonically isomorphic
pullback functors.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.Scheme.QCoh.DescentData.Pullback

variable {U V : Scheme.{u}}
variable {I : Type v} {J : Type w}
variable {Uᵢ : I → Scheme.{u}} {Vⱼ : J → Scheme.{u}}
variable {u : ∀ i, Uᵢ i ⟶ U} {v : ∀ j, Vⱼ j ⟶ V}
variable {base : U ⟶ V}

/-- Pulling back a quasi-coherent descent datum along a morphism of fixed-target scheme
families preserves quasi-coherence in every component. -/
instance functorOfHom_obj_isQuasicoherent
    (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
    (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base)
    (D : DescentData Vⱼ v) (i : I) :
    (((Pseudofunctor.DescentData.pullFunctor
      (F := Modules.descentPseudofunctor)
      (f := v) (p := base) (f' := u) (p' := gᵢ) comm).obj D.obj).obj i).IsQuasicoherent := sorry

/-- Pullback along a morphism of fixed-target scheme families, restricted to
quasi-coherent descent data. -/
noncomputable def functorOfHom
    (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
    (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base) :
    DescentData Vⱼ v ⥤ DescentData Uᵢ u :=
  ObjectProperty.lift
    (descentProperty Uᵢ u)
    ((descentProperty Vⱼ v).ι ⋙
      Pseudofunctor.DescentData.pullFunctor
        (F := Modules.descentPseudofunctor)
        (f := v) (p := base) (f' := u) (p' := gᵢ) comm)
    (fun D i ↦ functorOfHom_obj_isQuasicoherent α gᵢ comm D i)

/-- The component of the pulled quasi-coherent descent datum at `i` is module pullback along
the corresponding component of the family morphism. -/
theorem functorOfHom_obj_obj
    (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
    (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base)
    (D : DescentData Vⱼ v) (i : I) :
    ((functorOfHom α gᵢ comm).obj D).obj.obj i =
      (Modules.pullback (gᵢ i)).obj (D.obj.obj (α i)) := sorry

/-- On transition maps, quasi-coherent pullback retains the transition map of the canonical
pullback construction on the underlying module descent datum. -/
theorem functorOfHom_obj_hom
    (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
    (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base)
    (D : DescentData Vⱼ v) {Y : Scheme.{u}} (q : Y ⟶ U) {i j : I}
    (f₁ : Y ⟶ Uᵢ i) (f₂ : Y ⟶ Uᵢ j)
    (hf₁ : f₁ ≫ u i = q) (hf₂ : f₂ ≫ u j = q) :
    ((functorOfHom α gᵢ comm).obj D).obj.hom q f₁ f₂ hf₁ hf₂ =
      Pseudofunctor.DescentData.pullFunctorObjHom
        (F := Modules.descentPseudofunctor)
        (f := v) (p := base) (f' := u) (α := α) (p' := gᵢ) (w := comm)
        D.obj q f₁ f₂ hf₁ hf₂ := sorry

/-- On morphisms, quasi-coherent pullback is the canonical pullback of each component map. -/
theorem functorOfHom_map_hom
    (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
    (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base)
    {D E : DescentData Vⱼ v} (η : D ⟶ E) (i : I) :
    ((functorOfHom α gᵢ comm).map η).hom.hom i =
      (Modules.pullback (gᵢ i)).map (η.hom.hom (α i)) := sorry

/-- Two morphisms of fixed-target scheme families over the same base map induce naturally
isomorphic pullback functors on quasi-coherent descent data. -/
noncomputable def isoOfHom
    (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
    (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base)
    (α' : I → J) (gᵢ' : ∀ i, Uᵢ i ⟶ Vⱼ (α' i))
    (comm' : ∀ i, gᵢ' i ≫ v (α' i) = u i ≫ base) :
    functorOfHom α gᵢ comm ≅ functorOfHom α' gᵢ' comm' :=
  ((descentProperty Uᵢ u).fullyFaithfulι.whiskeringRight _).preimageIso
      ((descentProperty Vⱼ v).ι.isoWhiskerLeft
        (Pseudofunctor.DescentData.pullFunctorIso
          (F := Modules.descentPseudofunctor)
          (f := v) (p := base) (f' := u) (α := α) (p' := gᵢ) (w := comm)
          (β := α') (p'' := gᵢ') comm'))

/-- The underlying component of the quasi-coherent comparison is the canonical same-base
comparison for module descent data. -/
theorem isoOfHom_hom_app_hom
    (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
    (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base)
    (α' : I → J) (gᵢ' : ∀ i, Uᵢ i ⟶ Vⱼ (α' i))
    (comm' : ∀ i, gᵢ' i ≫ v (α' i) = u i ≫ base)
    (D : DescentData Vⱼ v) (i : I) :
    ((isoOfHom α gᵢ comm α' gᵢ' comm').hom.app D).hom.hom i =
      ((Pseudofunctor.DescentData.pullFunctorIso
        (F := Modules.descentPseudofunctor)
        (f := v) (p := base) (f' := u) (α := α) (p' := gᵢ) (w := comm)
        (β := α') (p'' := gᵢ') comm').hom.app D.obj).hom i := sorry

end AlgebraicGeometry.Scheme.QCoh.DescentData.Pullback
