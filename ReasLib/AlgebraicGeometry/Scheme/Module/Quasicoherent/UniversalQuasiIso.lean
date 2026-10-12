/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Basic

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh.pullback

/-- Pullback of quasicoherent modules along a scheme morphism is additive. -/
instance additive {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.QCoh.pullback f).Additive := sorry

end AlgebraicGeometry.Scheme.QCoh.pullback

namespace AlgebraicGeometry.Scheme.QCoh

/-- Morphisms of bounded-below quasicoherent complexes that become
quasi-isomorphisms after pullback along every morphism of schemes. -/
noncomputable def universalQuasiIso (S : Scheme.{u}) :
    MorphismProperty (HomotopyCategory.Plus (Scheme.QCoh S)) :=
  ⨅ (T : Scheme.{u}) (f : T ⟶ S),
    (HomotopyCategory.Plus.quasiIso (Scheme.QCoh T)).inverseImage
      (Scheme.QCoh.pullback f).mapHomotopyCategoryPlus

/-- Membership in `universalQuasiIso S` is the condition of becoming a
quasi-isomorphism after every scheme pullback. -/
theorem universalQuasiIso_iff (S : Scheme.{u})
    {K L : HomotopyCategory.Plus (Scheme.QCoh S)} (g : K ⟶ L) :
    universalQuasiIso S g ↔
      ∀ (T : Scheme.{u}) (f : T ⟶ S),
        HomotopyCategory.Plus.quasiIso (Scheme.QCoh T)
          ((Scheme.QCoh.pullback f).mapHomotopyCategoryPlus.map g) := sorry

/-- Every universal quasi-isomorphism is a quasi-isomorphism. -/
theorem universalQuasiIso_le_quasiIso (S : Scheme.{u}) :
    universalQuasiIso S ≤ HomotopyCategory.Plus.quasiIso (Scheme.QCoh S) := sorry

end AlgebraicGeometry.Scheme.QCoh
