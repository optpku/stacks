/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Opposites
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Residue

/-!
# Spectra of Artinian local algebras as objects of `Over S`

A chosen affine open `Spec(Λ) ⊂ S` sends an object `A` of `ArtinianLocalAlgCat Λ k`
to the factorization `Spec(A) ⟶ S` through that open, and sends a morphism of
Artinian local `Λ`-algebras to the reversed morphism in `Over S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]

/-- The object `Spec(A) ⟶ S` of `Over S` obtained by composing `Spec` of the structure
map `Λ → A` with the chosen affine open `Spec(Λ) ⟶ S`. -/
def specOver (A : ArtinianLocalAlgCat Λ k) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A.carrier)) ≫ openImmersion)

/-- `specOver A` is the morphism `Spec(A) ⟶ S` through `Spec(Λ)`. -/
theorem specOver_obj (A : ArtinianLocalAlgCat Λ k) :
    (specOver openImmersion A).left = Spec (CommRingCat.of A.carrier) ∧
      (specOver openImmersion A).hom =
        Spec.map (CommRingCat.ofHom (algebraMap Λ A.carrier)) ≫ openImmersion :=
  sorry

/-- A morphism `A ⟶ B` in `ArtinianLocalAlgCat` is compatible with the two
structure morphisms `Spec(A) ⟶ S` and `Spec(B) ⟶ S`. -/
theorem specOverMap_comp {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap Λ A.carrier)) ≫ openImmersion) =
      Spec.map (CommRingCat.ofHom (algebraMap Λ B.carrier)) ≫ openImmersion :=
  sorry

/-- The morphism `Spec(B) ⟶ Spec(A)` over `S` induced by `f : A ⟶ B`. -/
def specOverMap {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    specOver openImmersion B ⟶ specOver openImmersion A :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.hom.toRingHom)) (specOverMap_comp openImmersion f)

/-- `specOverMap f` is `Spec` of the underlying ring map of `f`, as a morphism of
`Over S`. -/
theorem specOverMap_spec {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    (specOverMap openImmersion f).left = Spec.map (CommRingCat.ofHom f.hom.toRingHom) ∧
      Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ (specOver openImmersion A).hom =
        (specOver openImmersion B).hom :=
  sorry

variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]

/-- The residue morphism `A ⟶ k` is compatible with `kToS` and the structure
morphism `Spec(A) ⟶ S`. -/
theorem specOver_toResidue_comp
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (A : ArtinianLocalAlgCat Λ k) :
    Spec.map (CommRingCat.ofHom (ArtinianLocalAlgCat.toResidue A).hom.toRingHom) ≫
        (specOver openImmersion A).hom = kToS :=
  sorry

/-- The canonical morphism `Spec(k) ⟶ Spec(A)` over `S`, induced by
`ArtinianLocalAlgCat.toResidue`. -/
def specOver_toResidue
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (A : ArtinianLocalAlgCat Λ k) :
    Over.mk kToS ⟶ specOver openImmersion A :=
  Over.homMk (Spec.map (CommRingCat.ofHom (ArtinianLocalAlgCat.toResidue A).hom.toRingHom))
    (specOver_toResidue_comp openImmersion kToS h_factor A)

/-- `specOver_toResidue A` is `Spec` of `toResidue A` as a morphism
`Over.mk kToS ⟶ specOver A`. -/
theorem specOver_toResidue_spec
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (A : ArtinianLocalAlgCat Λ k) :
    (specOver_toResidue openImmersion kToS h_factor A).left =
        Spec.map (CommRingCat.ofHom (ArtinianLocalAlgCat.toResidue A).hom.toRingHom) ∧
      Spec.map (CommRingCat.ofHom (ArtinianLocalAlgCat.toResidue A).hom.toRingHom) ≫
          (specOver openImmersion A).hom = kToS :=
  sorry

/-- The comparison `ArtinianLocalAlgCat Λ k ⥤ (Over S)ᵒᵖ` sending `A` to
`Spec(A) ⟶ S` through the chosen affine open. -/
def specFunctor : ArtinianLocalAlgCat Λ k ⥤ (Over S)ᵒᵖ where
  obj A := .op (specOver openImmersion A)
  map f := (specOverMap openImmersion f).op
  map_id := sorry
  map_comp := sorry

/-- The object map of `specFunctor` is `specOver`. -/
theorem specFunctor_obj (A : ArtinianLocalAlgCat Λ k) :
    (specFunctor openImmersion).obj A = .op (specOver openImmersion A) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
