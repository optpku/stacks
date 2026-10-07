module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.RingTheory.Artinian.Defs
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap69.Definition_69_12_1_Instances

/-!
# Artinian-spectrum coherent pushforwards on algebraic spaces

Quasi-coherent modules on an algebraic space that are isomorphic to the
pushforward of a coherent module from the spectrum of an Artinian ring.
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
  sorry

/-- A quasi-coherent module isomorphic to the pushforward of a coherent module from the
spectrum of an Artinian ring satisfies `isArtinianSpecCoherentPushforward`. -/
theorem of_pushforward {S : Scheme.{u}} {X : AlgebraicSpace S} {A : CommRingCat.{u}}
    [IsArtinianRing A] {σ : Spec A ⟶ S} (f : ofOver (Over.mk σ) ⟶ X)
    (G : (ofOver (Over.mk σ)).Modules) [G.IsCoherent] {F : QCoh X}
    (e : F.obj ≅ (Modules.pushforward f).obj G) :
    isArtinianSpecCoherentPushforward X F :=
  sorry

end isArtinianSpecCoherentPushforward

end AlgebraicGeometry.AlgebraicSpace.QCoh
