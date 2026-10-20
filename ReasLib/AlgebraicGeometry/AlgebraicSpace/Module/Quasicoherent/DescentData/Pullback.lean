/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.DescentData

/-!
# Pullback of quasi-coherent descent data along morphisms of algebraic-space families

A morphism between fixed-target families of algebraic spaces induces pullback on
quasi-coherent descent data. Morphisms of families over the same base map induce
canonically isomorphic pullback functors.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry.AlgebraicSpace

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Pullback

variable {S : Scheme.{u}}
variable {U V : AlgebraicSpace S}

section Unbundled

variable {I : Type v} {J : Type w}
variable {Uᵢ : I → AlgebraicSpace S} {Vⱼ : J → AlgebraicSpace S}
variable {u : ∀ i, Uᵢ i ⟶ U} {v : ∀ j, Vⱼ j ⟶ V}
variable {base : U ⟶ V}

/-- Pulling back a quasi-coherent descent datum along a morphism of fixed-target
algebraic-space families preserves quasi-coherence in every component. -/
instance functorOfHom_obj_isQuasicoherent
    (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
    (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base)
    (D : DescentData Vⱼ v) (i : I) :
    (((Pseudofunctor.DescentData.pullFunctor
      (F := Modules.descentPseudofunctor S)
      (f := v) (p := base) (f' := u) (p' := gᵢ) comm).obj D.obj).obj i).IsQuasicoherent := sorry

/-- Pullback along a morphism of fixed-target algebraic-space families, restricted to
quasi-coherent descent data. -/
noncomputable def functorOfHom
    (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
    (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base) :
    DescentData Vⱼ v ⥤ DescentData Uᵢ u :=
  ObjectProperty.lift
    (descentProperty Uᵢ u)
    ((descentProperty Vⱼ v).ι ⋙
      Pseudofunctor.DescentData.pullFunctor
        (F := Modules.descentPseudofunctor S)
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
    (D : DescentData Vⱼ v) {Y : AlgebraicSpace S} (q : Y ⟶ U) {i j : I}
    (f₁ : Y ⟶ Uᵢ i) (f₂ : Y ⟶ Uᵢ j)
    (hf₁ : f₁ ≫ u i = q) (hf₂ : f₂ ≫ u j = q) :
    ((functorOfHom α gᵢ comm).obj D).obj.hom q f₁ f₂ hf₁ hf₂ =
      Pseudofunctor.DescentData.pullFunctorObjHom
        (F := Modules.descentPseudofunctor S)
        (f := v) (p := base) (f' := u) (α := α) (p' := gᵢ) (w := comm)
        D.obj q f₁ f₂ hf₁ hf₂ := sorry

/-- On morphisms, quasi-coherent pullback is the canonical pullback of each component map. -/
theorem functorOfHom_map_hom
    (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
    (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base)
    {D E : DescentData Vⱼ v} (η : D ⟶ E) (i : I) :
    ((functorOfHom α gᵢ comm).map η).hom.hom i =
      (Modules.pullback (gᵢ i)).map (η.hom.hom (α i)) := sorry

/-- Two morphisms of fixed-target algebraic-space families over the same base map induce
naturally isomorphic pullback functors on quasi-coherent descent data. -/
noncomputable def isoOfHom
    (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
    (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base)
    (α' : I → J) (gᵢ' : ∀ i, Uᵢ i ⟶ Vⱼ (α' i))
    (comm' : ∀ i, gᵢ' i ≫ v (α' i) = u i ≫ base) :
    functorOfHom α gᵢ comm ≅ functorOfHom α' gᵢ' comm' :=
  ((descentProperty Uᵢ u).fullyFaithfulι.whiskeringRight _).preimageIso
      ((descentProperty Vⱼ v).ι.isoWhiskerLeft
        (Pseudofunctor.DescentData.pullFunctorIso
          (F := Modules.descentPseudofunctor S)
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
        (F := Modules.descentPseudofunctor S)
        (f := v) (p := base) (f' := u) (α := α) (p' := gᵢ) (w := comm)
        (β := α') (p'' := gᵢ') comm').hom.app D.obj).hom i := sorry

end Unbundled

end AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Pullback
