module

public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineTypes
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineMorphism

/-!
# Flat morphisms of affine formal algebraic spaces

A morphism of affine formal algebraic spaces corresponds to a flat map of
adic Noetherian topological rings when it is induced by a continuous
homomorphism `φ : A →+* B` that is flat as a ring homomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- A morphism of affine formal algebraic spaces is flat when it is induced by
a flat continuous homomorphism of adic Noetherian topological rings. -/
class Flat {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace V]
    [FormalAlgebraicSpace.IsAffine V]
    (g : U ⟶ V) : Prop where
  /-- There is a flat homomorphism of adic Noetherian rings inducing `g`. -/
  exists_hom :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
      (_ : TopologicalSpace A) (_ : TopologicalSpace B)
      (_ : TopologicalRing.IsAdicRing A) (_ : TopologicalRing.IsAdicRing B)
      (_ : IsNoetherianRing A) (_ : IsNoetherianRing B)
      (φ : A →+* B),
        φ.Flat ∧ IsInducedBy g φ

namespace Flat

/-- The identity of a Noetherian affine formal algebraic space is flat. -/
instance id {S : Scheme.{u}} {U : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsNoetherianAffine U] : Flat (𝟙 U) :=
  sorry

/-- A morphism induced by a flat homomorphism of adic Noetherian rings is
flat. -/
theorem ofHom {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace V]
    [FormalAlgebraicSpace.IsAffine V]
    (g : U ⟶ V) {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B)
    (hφ : φ.Flat) (hg : IsInducedBy g φ) : Flat g :=
  sorry

/-- A flat morphism of affine formal algebraic spaces is induced by a flat
homomorphism of adic Noetherian rings. -/
theorem spec {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace V]
    [FormalAlgebraicSpace.IsAffine V]
    (g : U ⟶ V) [Flat g] :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
      (_ : TopologicalSpace A) (_ : TopologicalSpace B)
      (_ : TopologicalRing.IsAdicRing A) (_ : TopologicalRing.IsAdicRing B)
      (_ : IsNoetherianRing A) (_ : IsNoetherianRing B)
      (φ : A →+* B),
        φ.Flat ∧ IsInducedBy g φ :=
  sorry

/-- Flatness of a morphism of affine formal algebraic spaces is equivalent to
being induced by a flat homomorphism of adic Noetherian rings. -/
theorem iff {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace V]
    [FormalAlgebraicSpace.IsAffine V]
    (g : U ⟶ V) :
    Flat g ↔
      ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
        (_ : TopologicalSpace A) (_ : TopologicalSpace B)
        (_ : TopologicalRing.IsAdicRing A) (_ : TopologicalRing.IsAdicRing B)
        (_ : IsNoetherianRing A) (_ : IsNoetherianRing B)
        (φ : A →+* B),
          φ.Flat ∧ IsInducedBy g φ :=
  sorry

end Flat

end AlgebraicGeometry.AffineFormalAlgebraicSpace

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A morphism between explicitly specified affine formal algebraic spaces
is flat when it is induced by a flat continuous map of adic Noetherian rings. -/
def isFlatArrow {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    (hU : IsFormalAlgebraicSpace U) (hUaff : IsAffine U)
    (hV : IsFormalAlgebraicSpace V) (hVaff : IsAffine V)
    (g : U ⟶ V) : Prop :=
  @AffineFormalAlgebraicSpace.Flat S U V hU hUaff hV hVaff g

/-- Flatness with explicit affine and formal hypotheses is equivalent to
affine formal flatness with those hypotheses as instance arguments. -/
theorem isFlatArrow_iff {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    (hU : IsFormalAlgebraicSpace U) (hUaff : IsAffine U)
    (hV : IsFormalAlgebraicSpace V) (hVaff : IsAffine V)
    (g : U ⟶ V) :
    isFlatArrow hU hUaff hV hVaff g ↔
      @AffineFormalAlgebraicSpace.Flat S U V hU hUaff hV hVaff g :=
  Iff.rfl

end AlgebraicGeometry.FormalAlgebraicSpace
