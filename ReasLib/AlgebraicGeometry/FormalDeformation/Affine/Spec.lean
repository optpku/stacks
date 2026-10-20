module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Affine

/-!
# Spectrum of algebra deformations

Spectrum sends a flat algebra deformation to its associated flat scheme deformation
and preserves the Artinian base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped AlgebraicGeometry BasedFunctor

noncomputable section

universe u

namespace FlatSchemeCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The structure morphism `Spec Q ⟶ Spec A` of a flat algebra pair. -/
def specStructureHomOf (Y : FlatAlgebraCat Λ k) :
    Spec (CommRingCat.of Y.algebra) ⟶ Spec (CommRingCat.of Y.base.carrier) :=
  Spec.map (CommRingCat.ofHom (algebraMap Y.base.carrier Y.algebra))

/-- `Spec.map` of a flat algebra map is a flat morphism of schemes. -/
instance instFlat_specStructureHomOf (Y : FlatAlgebraCat Λ k) :
    AlgebraicGeometry.Flat (specStructureHomOf Y) :=
  sorry

/-- The affine scheme pair `(A, Spec Q)` attached to a flat algebra pair `(A, Q)`. -/
def specPairOf (Y : FlatAlgebraCat Λ k) : FlatSchemeCat Λ k :=
  of Y.base (Spec (CommRingCat.of Y.algebra)) (specStructureHomOf Y)
    (instFlat_specStructureHomOf Y)

/-- `specPairOf` keeps the stored Artinian base. -/
theorem specPairOf_base (Y : FlatAlgebraCat Λ k) : (specPairOf Y).base = Y.base :=
  rfl

/-- The scheme morphism attached to a morphism of flat algebra pairs. -/
def specPairMap {Q P : FlatAlgebraCat Λ k} (f : Q ⟶ P) : specPairOf Q ⟶ specPairOf P :=
  Hom.of f.baseHom (Spec.map (CommRingCat.ofHom f.toRingHom)) sorry

/-- `specPairMap` preserves the underlying morphism of Artinian local algebras. -/
theorem specPairMap_baseHom {Q P : FlatAlgebraCat Λ k} (f : Q ⟶ P) :
    (specPairMap f).baseHom = f.baseHom :=
  rfl

variable (Λ k) (P : Type u) [CommRing P] [Algebra k P]

/-- The residue morphism `(A, Spec Q) ⟶ (k, Spec P)` of a deformation of `P`. -/
def specResidueHom (ξ : FlatAlgebraCat.deformationCategory Λ k P) :
    specPairOf ξ.left ⟶ ofResidue Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P) :=
  Hom.of ξ.hom.baseHom (Spec.map (CommRingCat.ofHom ξ.hom.toRingHom)) sorry

/-- The ordinary functor `Def_P ⥤ Def_{Spec P}` sending `(A, Q)` to `(A, Spec Q)`. -/
def specFunctor :
    FlatAlgebraCat.deformationCategory Λ k P ⥤
      deformationCategory Λ k (Spec (CommRingCat.of P)) (specStructureHom Λ k P) := by
  have certificates :
      (∀ {ξ η : FlatAlgebraCat.deformationCategory Λ k P} (φ : ξ ⟶ η),
        specPairMap φ.left ≫ specResidueHom Λ k P η = specResidueHom Λ k P ξ) ∧
      (∀ ξ : FlatAlgebraCat.deformationCategory Λ k P,
        specPairMap (𝟙 ξ : ξ ⟶ ξ).left = 𝟙 (specPairOf ξ.left)) ∧
      (∀ {ξ η ζ : FlatAlgebraCat.deformationCategory Λ k P} (φ : ξ ⟶ η) (ψ : η ⟶ ζ),
        specPairMap (φ ≫ ψ).left = specPairMap φ.left ≫ specPairMap ψ.left) := sorry
  exact {
    obj := fun ξ ↦ Over.mk (specResidueHom Λ k P ξ)
    map := fun φ ↦ Over.homMk (specPairMap φ.left) (certificates.1 φ)
    map_id := fun ξ ↦ by apply Over.OverMorphism.ext; exact certificates.2.1 ξ
    map_comp := fun φ ψ ↦ by apply Over.OverMorphism.ext; exact certificates.2.2 φ ψ }

/-- Objects of `specFunctor` keep the stored Artinian base. -/
theorem specFunctor_obj_left_base (ξ : FlatAlgebraCat.deformationCategory Λ k P) :
    ((specFunctor Λ k P).obj ξ).left.base = ξ.left.base :=
  rfl

/-- `specFunctor` lies strictly over `ArtinianLocalAlgCat`. -/
theorem specFunctor_comp_forget :
    specFunctor Λ k P ⋙ schemeDeformationForget Λ k P = algebraDeformationForget Λ k P :=
  sorry

/-- The based functor `Def_P ⥤ᵇ Def_{Spec P}` sending `(A, Q)` to `(A, Spec Q)`. -/
def specBasedFunctor :
    BasedCategory.ofFunctor (algebraDeformationForget Λ k P) ⥤ᵇ
      BasedCategory.ofFunctor (schemeDeformationForget Λ k P) :=
  BasedFunctor.ofFunctor (specFunctor Λ k P) (specFunctor_comp_forget Λ k P)

/-- The underlying ordinary functor of `specBasedFunctor` is `specFunctor`. -/
theorem specBasedFunctor_toFunctor :
    (specBasedFunctor Λ k P).toFunctor = specFunctor Λ k P :=
  rfl

end FlatSchemeCat

