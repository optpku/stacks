module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.RingTheory.Artinian.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category

/-!
# Artinian-spectrum coherent pushforwards on algebraic spaces

Quasi-coherent modules on an algebraic space that are isomorphic to the
pushforward of a coherent module from the spectrum of an Artinian ring,
and retracts of their filtered colimits.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

/-- The object property of quasi-coherent modules isomorphic to the pushforward of a
coherent module along a morphism from the spectrum of an Artinian ring. -/
def isArtinianSpecCoherentPushforward {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ObjectProperty (QCoh X) :=
  fun F ↦
    ∃ (A : CommRingCat.{u}) (_ : IsArtinianRing A) (σ : Spec A ⟶ S)
      (f : ofOver (Over.mk σ) ⟶ X) (G : (ofOver (Over.mk σ)).Modules) (_ : G.IsCoherent),
      Nonempty (F.obj ≅ (Modules.pushforward f).obj G)

namespace isArtinianSpecCoherentPushforward

/-- Membership in `isArtinianSpecCoherentPushforward` unpacks as an isomorphism with the
pushforward of a coherent module along a morphism from the spectrum of an Artinian ring. -/
theorem mem_iff {S : Scheme.{u}} {X : AlgebraicSpace S} {F : QCoh X} :
    isArtinianSpecCoherentPushforward X F ↔
      ∃ (A : CommRingCat.{u}) (_ : IsArtinianRing A) (σ : Spec A ⟶ S)
        (f : ofOver (Over.mk σ) ⟶ X) (G : (ofOver (Over.mk σ)).Modules) (_ : G.IsCoherent),
        Nonempty (F.obj ≅ (Modules.pushforward f).obj G) :=
  Iff.rfl

/-- A quasi-coherent module isomorphic to the pushforward of a coherent module from the
spectrum of an Artinian ring satisfies `isArtinianSpecCoherentPushforward`. -/
theorem of_pushforward {S : Scheme.{u}} {X : AlgebraicSpace S} {A : CommRingCat.{u}}
    [IsArtinianRing A] {σ : Spec A ⟶ S} (f : ofOver (Over.mk σ) ⟶ X)
    (G : (ofOver (Over.mk σ)).Modules) [G.IsCoherent] {F : QCoh X}
    (e : F.obj ≅ (Modules.pushforward f).obj G) :
    isArtinianSpecCoherentPushforward X F :=
  ⟨A, inferInstance, σ, f, G, inferInstance, ⟨e⟩⟩

end isArtinianSpecCoherentPushforward

/-- Every injective quasi-coherent module on a Noetherian algebraic space over an affine
scheme is a direct summand of a small filtered colimit of quasi-coherent modules isomorphic
to pushforwards of coherent modules from spectra of Artinian rings. -/
theorem injective_retractClosure_ind_artinianSpecCoherentPushforward
    {S : Scheme.{u}} [IsAffine S] {X : AlgebraicSpace S} [IsNoetherian X]
    (J : QCoh X) [Injective J] :
    (isArtinianSpecCoherentPushforward X).ind.{u}.retractClosure J :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QCoh
