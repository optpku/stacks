/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Artinian.Defs
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent

/-!
# Artinian-spectrum coherent pushforwards

Quasi-coherent modules on a scheme that are isomorphic to the pushforward of a
coherent module from the spectrum of an Artinian ring, and their filtered colimits.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/-- The object property of quasi-coherent modules isomorphic to the pushforward of a
coherent module along a morphism from the spectrum of an Artinian ring. -/
def isArtinianSpecCoherentPushforward (S : Scheme.{u}) : ObjectProperty (QCoh S) :=
  fun F ↦
    ∃ (A : CommRingCat.{u}) (_ : IsArtinianRing A) (f : Spec A ⟶ S)
      (G : (Spec A).Modules) (_ : G.IsCoherent),
      Nonempty (F.obj ≅ (Modules.pushforward f).obj G)

namespace isArtinianSpecCoherentPushforward

/-- Membership in `isArtinianSpecCoherentPushforward` unpacks as an isomorphism with the
pushforward of a coherent module along a morphism from the spectrum of an Artinian ring. -/
theorem mem_iff {S : Scheme.{u}} {F : QCoh S} :
    isArtinianSpecCoherentPushforward S F ↔
      ∃ (A : CommRingCat.{u}) (_ : IsArtinianRing A) (f : Spec A ⟶ S)
        (G : (Spec A).Modules) (_ : G.IsCoherent),
        Nonempty (F.obj ≅ (Modules.pushforward f).obj G) :=
  sorry

/-- A quasi-coherent module isomorphic to the pushforward of a coherent module from the
spectrum of an Artinian ring satisfies `isArtinianSpecCoherentPushforward`. -/
theorem of_pushforward {S : Scheme.{u}} {A : CommRingCat.{u}} [IsArtinianRing A]
    (f : Spec A ⟶ S) (G : (Spec A).Modules) [G.IsCoherent] {F : QCoh S}
    (e : F.obj ≅ (Modules.pushforward f).obj G) :
    isArtinianSpecCoherentPushforward S F :=
  sorry

end isArtinianSpecCoherentPushforward

/-- Every injective quasi-coherent module on a Noetherian affine scheme is a small
filtered colimit of quasi-coherent modules isomorphic to pushforwards of coherent
modules from spectra of Artinian rings. -/
theorem injective_ind_artinianSpecCoherentPushforward
    {S : Scheme.{u}} [IsAffine S] [IsNoetherian S] (J : QCoh S) [Injective J] :
    (isArtinianSpecCoherentPushforward S).ind.{u} J :=
  sorry

end AlgebraicGeometry.Scheme.QCoh
