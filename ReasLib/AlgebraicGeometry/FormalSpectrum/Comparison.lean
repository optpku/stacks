/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.Colimit
public import Mathlib.RingTheory.LocalRing.Defs

/-!
# Comparison from Spf to Spec

The canonical morphism `Spf(A) ⟶ Spec(A)` of sheaves over `S` is the colimit
of the sheafified Yoneda images of the affine stages `Spec(A ⧸ I) ⟶ Spec(A)`.
Precomposition yields the natural map on morphisms into an `S`-scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The morphism of schemes over `S` from the affine stage `Spec(A ⧸ I)` to
`Spec(A)`. -/
def stageToSpec {A : Type u} [CommRing A] [TopologicalSpace A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) (I : WeakIdealOfDefinition A) :
    stage A structureHom I ⟶ Over.mk structureHom :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I.ideal))) rfl

/-- The underlying scheme morphism of `stageToSpec` is `Spec` of the quotient
map `A →+* A ⧸ I`. -/
theorem stageToSpec_left {A : Type u} [CommRing A] [TopologicalSpace A]
    {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    (I : WeakIdealOfDefinition A) :
    (stageToSpec structureHom I).left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I.ideal)) := sorry

/-- The comparison morphism `Spf(A) ⟶ Spec(A)` of sheaves over `S`. -/
def spfToSpec {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    spf A structureHom ⟶
      (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).obj
        (yoneda.obj (Over.mk structureHom)) :=
  colimit.desc
    (thickenings A structureHom ⋙ yoneda ⋙
      presheafToSheaf (Scheme.fppfTopology.over S) (Type u))
    { pt := (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).obj
        (yoneda.obj (Over.mk structureHom))
      ι :=
        { app I :=
            (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
              (yoneda.map (stageToSpec structureHom I))
          naturality := sorry } }

/-- The comparison `spfToSpec` restricts to the sheafified Yoneda image of
`stageToSpec` on each affine stage. -/
theorem spfToSpec_ι {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (I : WeakIdealOfDefinition A) :
    spfι A structureHom I ≫ spfToSpec structureHom =
      (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
        (yoneda.map (stageToSpec structureHom I)) := sorry

/-- The natural map `Mor_S(Spec(A), X) → Mor_S(Spf(A), X)` induced by
precomposition with `spfToSpec`. -/
def specHomToSpfHom {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) (X : Over S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    (Over.mk structureHom ⟶ X) →
      (spf A structureHom ⟶
        (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).obj
          (yoneda.obj X)) :=
  fun f ↦
    spfToSpec structureHom ≫
      (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map (yoneda.map f)

/-- `specHomToSpfHom` is precomposition with `spfToSpec` after sheafified
Yoneda. -/
theorem specHomToSpfHom_apply {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S) (X : Over S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (f : Over.mk structureHom ⟶ X) :
    specHomToSpfHom structureHom X f =
      spfToSpec structureHom ≫
        (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
          (yoneda.map f) := sorry

/-- For a weakly admissible topological ring over a scheme `S` and an affine
`S`-scheme `X`, precomposition with `Spf(A) ⟶ Spec(A)` is bijective on
morphisms into `X`. -/
theorem specHomToSpfHom_bijective {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    {X : Over S} [IsAffine X.left] :
    Function.Bijective (specHomToSpfHom structureHom X) := sorry

/-- For a weakly admissible topological ring over a scheme `S` with a local
quotient by a weak ideal of definition, precomposition with `Spf(A) ⟶ Spec(A)`
is bijective on morphisms into any `S`-scheme. -/
theorem specHomToSpfHom_bijective_of_isLocalRing {A : Type u} [CommRing A]
    [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    {S : Scheme.{u}} (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (I : WeakIdealOfDefinition A) [IsLocalRing (A ⧸ I.ideal)] {X : Over S} :
    Function.Bijective (specHomToSpfHom structureHom X) := sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
