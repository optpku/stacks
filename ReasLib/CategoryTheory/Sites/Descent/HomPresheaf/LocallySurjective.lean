/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.StrongTrans
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homwise locally surjective strong transformations

This file records the site-local surjectivity of the canonical Hom-presheaf maps induced by a
strong transformation. The property is stated for arbitrary `Cat`-valued pseudofunctors; fibred
categories and stacks use it through thin specialization layers.
-/

@[expose] public section

universe uC vC uP vP

namespace CategoryTheory.Pseudofunctor.StrongTrans

open Opposite
open scoped CategoryTheory.Bicategory Pseudofunctor.StrongTrans

variable {C : Type uC} [Category.{vC} C]
variable {P Q R : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP}}

/-- A strong transformation is homwise locally surjective when each induced map of canonical
Hom-presheaves is locally surjective on the corresponding slice site. -/
def Homwise.IsLocallySurjective
    (η : P ⟶ Q) (J : GrothendieckTopology C) : Prop :=
  ∀ {U : C} (x y : P.obj (.mk (op U))),
    Presheaf.IsLocallySurjective (J.over U) (η.presheafHomMap x y)

/-- The homwise condition is precisely local surjectivity of every canonical Hom-presheaf map. -/
theorem Homwise.isLocallySurjective_iff
    (η : P ⟶ Q) (J : GrothendieckTopology C) :
    Homwise.IsLocallySurjective η J ↔
      ∀ {U : C} (x y : P.obj (.mk (op U))),
        Presheaf.IsLocallySurjective (J.over U) (η.presheafHomMap x y) := sorry

/-- Every canonical Hom-presheaf map of a homwise locally surjective transformation is locally
surjective. -/
theorem Homwise.IsLocallySurjective.presheafHomMap
    {η : P ⟶ Q} {J : GrothendieckTopology C}
    (hη : Homwise.IsLocallySurjective η J)
    {U : C} (x y : P.obj (.mk (op U))) :
    Presheaf.IsLocallySurjective (J.over U) (η.presheafHomMap x y) := sorry

/-- The identity strong transformation is homwise locally surjective. -/
theorem Homwise.IsLocallySurjective.id
    (P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    (J : GrothendieckTopology C) :
    Homwise.IsLocallySurjective (𝟙 P) J := sorry

/-- Homwise locally surjective strong transformations are closed under vertical composition. -/
theorem Homwise.IsLocallySurjective.comp
    {η : P ⟶ Q} {θ : Q ⟶ R} {J : GrothendieckTopology C}
    (hη : Homwise.IsLocallySurjective η J)
    (hθ : Homwise.IsLocallySurjective θ J) :
    Homwise.IsLocallySurjective (η ≫ θ) J := sorry

/-- If a composite is homwise locally surjective, then the right factor is locally surjective on
Hom-presheaves whose endpoints lie in the image of the left factor. -/
theorem Homwise.IsLocallySurjective.rightOnImage_of_comp
    {η : P ⟶ Q} {θ : Q ⟶ R} {J : GrothendieckTopology C}
    (h : Homwise.IsLocallySurjective (η ≫ θ) J)
    {U : C} (x y : P.obj (.mk (op U))) :
    Presheaf.IsLocallySurjective (J.over U)
      (θ.presheafHomMap
        ((η.app (.mk (op U))).toFunctor.obj x)
        ((η.app (.mk (op U))).toFunctor.obj y)) := sorry

/-- Homwise local surjectivity is preserved when the topology is enlarged. -/
theorem Homwise.IsLocallySurjective.of_le
    {η : P ⟶ Q} {J K : GrothendieckTopology C} (hJK : J ≤ K)
    (hη : Homwise.IsLocallySurjective η J) :
    Homwise.IsLocallySurjective η K := sorry

/-- A strong transformation is homwise locally surjective when all its canonical Hom-presheaf
maps are isomorphisms. -/
theorem Homwise.IsLocallySurjective.of_isIso
    (η : P ⟶ Q) (J : GrothendieckTopology C)
    (hη : ∀ {U : C} (x y : P.obj (.mk (op U))), IsIso (η.presheafHomMap x y)) :
    Homwise.IsLocallySurjective η J := sorry

end CategoryTheory.Pseudofunctor.StrongTrans
