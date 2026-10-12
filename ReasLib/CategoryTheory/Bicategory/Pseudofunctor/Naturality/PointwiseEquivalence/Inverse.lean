/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseEquivalence.Components
public import ReasLib.CategoryTheory.Bicategory.Equivalence.Calculus.Mate

/-!
# Mate-defined inverses of pointwise equivalences

This leaf constructs the inverse strong transformation of pointwise-equivalence
data from mates of the original naturality isomorphisms and records its direct
computations.
-/

@[expose] public section

universe wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor.StrongTrans

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {D : Type uD} [Bicategory.{wD, vD} D]
variable {F G : Pseudofunctor B D}

namespace PointwiseEquivalence

variable {η : F ⟶ G}

/-- The naturality isomorphism of the pointwise inverse strong transformation.

It is the reverse of the general invertible mate of the original naturality square. -/
@[stacks 0040 "inverse naturality of a pointwise equivalence"]
def inverse.naturalityIso
    (h : PointwiseEquivalence η) {a b : B} (f : a ⟶ b) :
    G.map f ≫ h.invApp b ≅ h.invApp a ≫ F.map f :=
  (Bicategory.Equivalence.mateIso
    (h.app a) (h.app b) (η.naturality f)).symm

/-- The forward cell of inverse naturality is its explicit mate construction. -/
@[simp]
theorem inverse.naturalityIso.hom
    (h : PointwiseEquivalence η) {a b : B} (f : a ⟶ b) :
    (inverse.naturalityIso h f).hom =
      (Bicategory.mateEquiv (h.app a).symm.toAdjunction
        (h.app b).symm.toAdjunction).symm
          (η.naturality f).inv := sorry

/-- The inverse cell of inverse naturality is its explicit mate construction. -/
@[simp]
theorem inverse.naturalityIso.inv
    (h : PointwiseEquivalence η) {a b : B} (f : a ⟶ b) :
    (inverse.naturalityIso h f).inv =
      Bicategory.mateEquiv (h.app a).toAdjunction
        (h.app b).toAdjunction (η.naturality f).hom := sorry

/-- Inverse naturality is natural in `2`-morphisms of the source bicategory. -/
theorem inverse.naturalityIso.map₂
    (h : PointwiseEquivalence η)
    {a b : B} {f g : a ⟶ b} (γ : f ⟶ g) :
    G.map₂ γ ▷ h.invApp b ≫
        (inverse.naturalityIso h g).hom =
      (inverse.naturalityIso h f).hom ≫
        h.invApp a ◁ F.map₂ γ := sorry

/-- Inverse naturality satisfies the identity coherence equation. -/
theorem inverse.naturalityIso.id
    (h : PointwiseEquivalence η) (a : B) :
    (inverse.naturalityIso h (𝟙 a)).hom ≫
        h.invApp a ◁ (F.mapId a).hom =
      (G.mapId a).hom ▷ h.invApp a ≫
        (λ_ (h.invApp a)).hom ≫
        (ρ_ (h.invApp a)).inv := sorry

/-- Inverse naturality satisfies the composition coherence equation. -/
theorem inverse.naturalityIso.comp
    (h : PointwiseEquivalence η)
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (inverse.naturalityIso h (f ≫ g)).hom ≫
        h.invApp a ◁ (F.mapComp f g).hom =
      (G.mapComp f g).hom ▷ h.invApp c ≫
        (α_ _ _ _).hom ≫
        G.map f ◁ (inverse.naturalityIso h g).hom ≫
        (α_ _ _ _).inv ≫
        (inverse.naturalityIso h f).hom ▷ F.map g ≫
        (α_ _ _ _).hom := sorry

/-- The pointwise inverse of a pointwise-equivalence strong transformation is itself a strong
transformation. -/
@[stacks 0040 "inverse strong transformation of a pointwise equivalence"]
def inverse (h : PointwiseEquivalence η) : G ⟶ F where
  app := h.invApp
  naturality := inverse.naturalityIso h
  naturality_naturality := inverse.naturalityIso.map₂ h
  naturality_id := inverse.naturalityIso.id h
  naturality_comp := inverse.naturalityIso.comp h

/-- The component of the inverse strong transformation is the chosen pointwise inverse. -/
@[simp]
theorem inverse.app (h : PointwiseEquivalence η) (a : B) :
    h.inverse.app a = h.invApp a := sorry

/-- The naturality isomorphism of the inverse strong transformation is the mate-defined
isomorphism. -/
@[simp]
theorem inverse.naturality
    (h : PointwiseEquivalence η) {a b : B} (f : a ⟶ b) :
    h.inverse.naturality f = inverse.naturalityIso h f := sorry

/-- The forward naturality cell of the inverse strong transformation is the explicit
inverse-direction mate. -/
@[simp]
theorem inverse.naturality.hom
    (h : PointwiseEquivalence η) {a b : B} (f : a ⟶ b) :
    (h.inverse.naturality f).hom =
      (inverse.naturalityIso h f).hom := sorry

/-- The inverse naturality cell of the inverse strong transformation is the explicit
forward-direction mate. -/
@[simp]
theorem inverse.naturality.inv
    (h : PointwiseEquivalence η) {a b : B} (f : a ⟶ b) :
    (h.inverse.naturality f).inv =
      (inverse.naturalityIso h f).inv := sorry

/- Data audit (mathlib 4.32): `inverse.naturalityIso` delegates the invertible
mate construction and both inverse laws to `Bicategory.Equivalence.mateIso`.
The inverse strong transformation retains `invApp` literally; all deferred
content is mate compatibility or strong-naturality coherence. -/

end PointwiseEquivalence

end Pseudofunctor.StrongTrans

end CategoryTheory
