/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Over

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The canonical morphism between stalk-spectrum base changes induced by a
commutative square of schemes. -/
noncomputable def stalkPullbackMap {X' S' X S : Scheme.{u}}
    (f' : X' ⟶ S') (i : X' ⟶ X) (g : S' ⟶ S) (f : X ⟶ S)
    (sq : CommSq i f' f g) (s' : S') :
    pullback f' (S'.fromSpecStalk s') ⟶
      pullback f (S'.fromSpecStalk s' ≫ g) :=
  pullback.map f' (S'.fromSpecStalk s') f (S'.fromSpecStalk s' ≫ g)
    i (𝟙 _) g sq.w.symm (Category.id_comp _).symm

/-- The stalk pullback map is compatible with the projections to the source schemes. -/
@[reassoc]
theorem stalkPullbackMap_fst {X' S' X S : Scheme.{u}}
    (f' : X' ⟶ S') (i : X' ⟶ X) (g : S' ⟶ S) (f : X ⟶ S)
    (sq : CommSq i f' f g) (s' : S') :
    stalkPullbackMap f' i g f sq s' ≫ pullback.fst f (S'.fromSpecStalk s' ≫ g) =
      pullback.fst f' (S'.fromSpecStalk s') ≫ i := sorry

/-- The stalk pullback map preserves the projection to the spectrum of the local ring. -/
@[reassoc]
theorem stalkPullbackMap_snd {X' S' X S : Scheme.{u}}
    (f' : X' ⟶ S') (i : X' ⟶ X) (g : S' ⟶ S) (f : X ⟶ S)
    (sq : CommSq i f' f g) (s' : S') :
    stalkPullbackMap f' i g f sq s' ≫ pullback.snd f (S'.fromSpecStalk s' ≫ g) =
      pullback.snd f' (S'.fromSpecStalk s') := sorry

/-- The canonical stalk pullback map induced by étale horizontal morphisms is étale. -/
instance stalkPullbackMap_etale {X' S' X S : Scheme.{u}}
    (f' : X' ⟶ S') (i : X' ⟶ X) (g : S' ⟶ S) (f : X ⟶ S)
    [Etale i] [Etale g] (sq : CommSq i f' f g) (s' : S') :
    Etale (stalkPullbackMap f' i g f sq s') := sorry

end AlgebraicGeometry.Scheme.Hom
