module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineTypes
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineMorphism
public import ReasLib.RingTheory.AdicCompletion.RigFlat

/-!
# Rig-flat morphisms of affine formal algebraic spaces

A morphism of affine formal algebraic spaces corresponds to a rig-flat map of
adic Noetherian topological rings when it is induced by a continuous
homomorphism `φ : A →+* B` that is rig-flat as a homomorphism of adic
Noetherian topological rings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- A morphism of affine formal algebraic spaces is rig-flat when it is induced
by a rig-flat continuous homomorphism of adic Noetherian topological rings. -/
class RigFlat {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace V]
    [FormalAlgebraicSpace.IsAffine V]
    (g : U ⟶ V) : Prop where
  /-- There is a rig-flat homomorphism of adic Noetherian rings inducing `g`. -/
  exists_hom :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
      (_ : TopologicalSpace A) (_ : TopologicalSpace B)
      (_ : TopologicalRing.IsAdicRing A) (_ : TopologicalRing.IsAdicRing B)
      (_ : IsNoetherianRing A) (_ : IsNoetherianRing B)
      (φ : A →+* B),
        RingHom.RigFlat φ ∧ IsInducedBy g φ

namespace RigFlat

/-- The identity of a Noetherian affine formal algebraic space is rig-flat. -/
instance id {S : Scheme.{u}} {U : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsNoetherianAffine U] : RigFlat (𝟙 U) :=
  sorry

/-- A morphism induced by a rig-flat homomorphism of adic Noetherian rings is
rig-flat. -/
theorem ofHom {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace V]
    [FormalAlgebraicSpace.IsAffine V]
    (g : U ⟶ V) {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B)
    [RingHom.RigFlat φ] (hg : IsInducedBy g φ) : RigFlat g :=
  by
  constructor
  exact ⟨A, B, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, φ, inferInstance, hg⟩

/-- A rig-flat morphism of affine formal algebraic spaces is induced by a
rig-flat homomorphism of adic Noetherian rings. -/
theorem spec {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace V]
    [FormalAlgebraicSpace.IsAffine V]
    (g : U ⟶ V) [RigFlat g] :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
      (_ : TopologicalSpace A) (_ : TopologicalSpace B)
      (_ : TopologicalRing.IsAdicRing A) (_ : TopologicalRing.IsAdicRing B)
      (_ : IsNoetherianRing A) (_ : IsNoetherianRing B)
      (φ : A →+* B),
        RingHom.RigFlat φ ∧ IsInducedBy g φ :=
  RigFlat.exists_hom (g := g)

/-- Rig-flatness of a morphism of affine formal algebraic spaces is equivalent
to being induced by a rig-flat homomorphism of adic Noetherian rings. -/
theorem iff {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace V]
    [FormalAlgebraicSpace.IsAffine V]
    (g : U ⟶ V) :
    RigFlat g ↔
      ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
        (_ : TopologicalSpace A) (_ : TopologicalSpace B)
        (_ : TopologicalRing.IsAdicRing A) (_ : TopologicalRing.IsAdicRing B)
        (_ : IsNoetherianRing A) (_ : IsNoetherianRing B)
        (φ : A →+* B),
          RingHom.RigFlat φ ∧ IsInducedBy g φ :=
  ⟨fun h => h.exists_hom, fun h => ⟨h⟩⟩

end RigFlat

end AlgebraicGeometry.AffineFormalAlgebraicSpace
