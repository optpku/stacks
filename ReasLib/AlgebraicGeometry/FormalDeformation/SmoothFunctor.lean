/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Types.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal

/-!
# Smooth morphisms of set-valued functors on Artinian local algebras

A natural transformation of functors on `ArtinianLocalAlgCat Λ k` is smooth
when it has the Schlessinger lifting property along surjections.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.NatTrans

/-- Restriction along a morphism paired with the component of a transformation at the
source object. -/
def liftPair {F G : ArtinianLocalAlgCat Λ k ⥤ Type v} (η : F ⟶ G)
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    F.obj B → F.obj A × G.obj B :=
  fun x' ↦ (F.map f x', η.app B x')

/-- `liftPair η f x'` is the pair `(F.map f x', η.app B x')`. -/
theorem liftPair_apply {F G : ArtinianLocalAlgCat Λ k ⥤ Type v} (η : F ⟶ G)
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) (x' : F.obj B) :
    liftPair η f x' = (F.map f x', η.app B x') :=
  sorry

/-- The first factor of `liftPair η f x'` is the image of `x'` under `F.map f`. -/
theorem liftPair_fst {F G : ArtinianLocalAlgCat Λ k ⥤ Type v} (η : F ⟶ G)
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) (x' : F.obj B) :
    (liftPair η f x').1 = F.map f x' :=
  sorry

/-- The second factor of `liftPair η f x'` is the image of `x'` under `η` at `B`. -/
theorem liftPair_snd {F G : ArtinianLocalAlgCat Λ k ⥤ Type v} (η : F ⟶ G)
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) (x' : F.obj B) :
    (liftPair η f x').2 = η.app B x' :=
  sorry

/-- A morphism of set-valued functors is smooth when every compatible lifting problem
along a surjection has a solution. -/
class IsSmooth {F G : ArtinianLocalAlgCat Λ k ⥤ Type v} (η : F ⟶ G) : Prop where
  /-- Given compatible points over the source and target algebras, there is a lift. -/
  exists_lift {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) (hf : Function.Surjective f.hom)
      (x : F.obj A) (y : G.obj B) (h : η.app A x = G.map f y) :
      ∃ x' : F.obj B, liftPair η f x' = (x, y)

/-- The identity transformation of a set-valued functor is smooth. -/
instance instIsSmoothId {F : ArtinianLocalAlgCat Λ k ⥤ Type v} : IsSmooth (𝟙 F) :=
  sorry

/-- Smoothness is the existence of lifts along surjections. -/
theorem isSmooth_iff {F G : ArtinianLocalAlgCat Λ k ⥤ Type v} (η : F ⟶ G) :
    IsSmooth η ↔
      ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A), Function.Surjective f.hom →
        ∀ (x : F.obj A) (y : G.obj B), η.app A x = G.map f y →
          ∃ x' : F.obj B, liftPair η f x' = (x, y) :=
  sorry

end CategoryTheory.NatTrans
