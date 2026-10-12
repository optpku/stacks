/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Adjunction.SimplicialResolution.Contraction

/-!
@stack 08ND

# Contracting arbitrary realizations of adjunction resolutions

Any realization of the iterated comonad formulas is canonically isomorphic to the standard
augmented resolution. This leaf transports both endpoint contractions across that comparison
and retains the resulting concrete inverses and bundled homotopy equivalences.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.SimplicialObject
open Opposite
open scoped CategoryTheory.IteratedEndofunctor Simplicial

universe uA uS vA vS

namespace CategoryTheory.Adjunction.SimplicialResolution

variable {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
variable {U : S ⥤ A} {V : A ⥤ S}

/-- An arbitrary realization of the adjunction comonad formulas, postcomposed degreewise by
the right adjoint. -/
@[stacks 08ND "postcomposed arbitrary adjunction realization"]
noncomputable def postcompose.realization
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) :
    SimplicialObject.Augmented (A ⥤ S) :=
  SimplicialObject.Augmented.postcompose V
    (EndofunctorResolution.Realization.augmentation hX)

/-- An arbitrary realization of the adjunction comonad formulas, precomposed degreewise by
the left adjoint. -/
@[stacks 08ND "precomposed arbitrary adjunction realization"]
noncomputable def precompose.realization
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) :
    SimplicialObject.Augmented (S ⥤ A) :=
  SimplicialObject.Augmented.precompose U
    (EndofunctorResolution.Realization.augmentation hX)

/-- The augmented comparison from a postcomposed arbitrary realization to the canonical
postcomposed adjunction resolution. -/
@[stacks 08ND "postcomposed arbitrary-realization comparison"]
noncomputable def postcompose.realization.iso
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) :
    postcompose.realization adj hX ≅ postcompose adj :=
  Comonad.Realizes.augmentedIso.map hX
    ((SimplicialObject.Augmented.whiskeringRight
      (A := A) (C := A) (B := S)).obj V)

/-- The augmented comparison from a precomposed arbitrary realization to the canonical
precomposed adjunction resolution. -/
@[stacks 08ND "precomposed arbitrary-realization comparison"]
noncomputable def precompose.realization.iso
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) :
    precompose.realization adj hX ≅ precompose adj :=
  Comonad.Realizes.augmentedIso.map hX
    ((SimplicialObject.Augmented.whiskeringLeft
      (A := S) (C := A) (B := A)).obj U)

/-- The canonical last extra degeneracy transported to a postcomposed arbitrary realization. -/
@[stacks 08ND "last extra degeneracy on a postcomposed arbitrary realization"]
noncomputable def postcompose.realization.lastExtraDegeneracy
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) :
    SimplicialObject.Augmented.LastExtraDegeneracy
      (postcompose.realization adj hX) :=
  Comonad.Realizes.lastExtraDegeneracy hX
    ((SimplicialObject.Augmented.whiskeringRight
      (A := A) (C := A) (B := S)).obj V)
    (postcompose.lastExtraDegeneracy adj)

/-- The transported postcomposed zero-section is the canonical unit section conjugated by the
mapped realization isomorphism. -/
@[simp, stacks 08ND "zero-section on a postcomposed arbitrary realization"]
theorem postcompose.realization.lastExtraDegeneracy.s'
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) :
    (postcompose.realization.lastExtraDegeneracy adj hX).s' =
      (SimplicialObject.Augmented.point.mapIso
        (postcompose.realization.iso adj hX).symm).inv ≫
      postcompose.zeroSection adj ≫
      (SimplicialObject.Augmented.drop.mapIso
        (postcompose.realization.iso adj hX).symm).hom.app (op ⦋0⦌) := sorry

/-- Each transported postcomposed last degeneracy is the corresponding unit insertion
conjugated by the mapped realization isomorphism. -/
@[simp, stacks 08ND "last-degeneracy maps on a postcomposed arbitrary realization"]
theorem postcompose.realization.lastExtraDegeneracy.s
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) (n : ℕ) :
    (postcompose.realization.lastExtraDegeneracy adj hX).s n =
      (SimplicialObject.Augmented.drop.mapIso
        (postcompose.realization.iso adj hX).symm).inv.app (op ⦋n⦌) ≫
      postcompose.lastDegeneracy adj n ≫
      (SimplicialObject.Augmented.drop.mapIso
        (postcompose.realization.iso adj hX).symm).hom.app (op ⦋n + 1⦌) := sorry

/-- The canonical extra degeneracy transported to a precomposed arbitrary realization. -/
@[stacks 08ND "extra degeneracy on a precomposed arbitrary realization"]
noncomputable def precompose.realization.extraDegeneracy
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (precompose.realization adj hX) :=
  Comonad.Realizes.extraDegeneracy hX
    ((SimplicialObject.Augmented.whiskeringLeft
      (A := S) (C := A) (B := A)).obj U)
    (precompose.extraDegeneracy adj)

/-- The transported precomposed zero-section is the canonical unit section conjugated by the
mapped realization isomorphism. -/
@[simp, stacks 08ND "zero-section on a precomposed arbitrary realization"]
theorem precompose.realization.extraDegeneracy.s'
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) :
    (precompose.realization.extraDegeneracy adj hX).s' =
      (SimplicialObject.Augmented.point.mapIso
        (precompose.realization.iso adj hX).symm).inv ≫
      precompose.zeroSection adj ≫
      (SimplicialObject.Augmented.drop.mapIso
        (precompose.realization.iso adj hX).symm).hom.app (op ⦋0⦌) := sorry

/-- Each transported precomposed extra degeneracy is the corresponding unit insertion
conjugated by the mapped realization isomorphism. -/
@[simp, stacks 08ND "extra-degeneracy maps on a precomposed arbitrary realization"]
theorem precompose.realization.extraDegeneracy.s
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) (n : ℕ) :
    (precompose.realization.extraDegeneracy adj hX).s n =
      (SimplicialObject.Augmented.drop.mapIso
        (precompose.realization.iso adj hX).symm).inv.app (op ⦋n⦌) ≫
      precompose.extraDegeneracyMap adj n ≫
      (SimplicialObject.Augmented.drop.mapIso
        (precompose.realization.iso adj hX).symm).hom.app (op ⦋n + 1⦌) := sorry

/-- The inverse of the postcomposed augmentation for an arbitrary realization, supplied by its
transported last extra degeneracy. -/
@[stacks 08ND "inverse for a postcomposed arbitrary realization"]
noncomputable def postcompose.realization.inverse
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) :
    (const (A ⥤ S)).obj V ⟶
      (postcompose.realization adj hX).left :=
  (postcompose.realization.lastExtraDegeneracy adj hX).section_

/-- The augmentation of a postcomposed arbitrary realization followed by its transported
inverse is homotopic to the identity. -/
@[stacks 08ND "postcomposed arbitrary-realization homotopy at the source"]
theorem postcompose.realization.hom_inv_id
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) :
    Homotopic
      ((postcompose.realization adj hX).hom ≫
        postcompose.realization.inverse adj hX)
      (𝟙 (postcompose.realization adj hX).left) := sorry

/-- The transported inverse of a postcomposed arbitrary realization followed by its
augmentation is homotopic to the identity. -/
@[stacks 08ND "postcomposed arbitrary-realization homotopy at the target"]
theorem postcompose.realization.inv_hom_id
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) :
    Homotopic
      (postcompose.realization.inverse adj hX ≫
        (postcompose.realization adj hX).hom)
      (𝟙 ((const (A ⥤ S)).obj V)) := sorry

/-- The structured homotopy equivalence obtained by postcomposing any realization with the
right adjoint. -/
@[stacks 08ND "structured postcomposed arbitrary realization equivalence"]
noncomputable def postcompose.realization.homotopyEquiv
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) :
    HomotopyEquiv (postcompose.realization adj hX).left
      ((const (A ⥤ S)).obj V) :=
  (postcompose.realization.lastExtraDegeneracy adj hX).simplicialHomotopyEquiv

/-- The forward map of the postcomposed arbitrary-realization equivalence is its
augmentation. -/
@[simp, stacks 08ND "forward map of the postcomposed arbitrary-realization equivalence"]
theorem postcompose.realization.homotopyEquiv.hom
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) :
    (postcompose.realization.homotopyEquiv adj hX).hom =
      (postcompose.realization adj hX).hom := sorry

/-- The inverse map of the postcomposed arbitrary-realization equivalence is the transported
unit-induced inverse. -/
@[simp, stacks 08ND "inverse map of the postcomposed arbitrary-realization equivalence"]
theorem postcompose.realization.homotopyEquiv.inv
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) :
    (postcompose.realization.homotopyEquiv adj hX).inv =
      postcompose.realization.inverse adj hX := sorry

/-- The inverse of the precomposed augmentation for an arbitrary realization, supplied by its
transported extra degeneracy. -/
@[stacks 08ND "inverse for a precomposed arbitrary realization"]
noncomputable def precompose.realization.inverse
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) :
    (const (S ⥤ A)).obj U ⟶
      (precompose.realization adj hX).left :=
  (precompose.realization.extraDegeneracy adj hX).section_

/-- The augmentation of a precomposed arbitrary realization followed by its transported
inverse is homotopic to the identity. -/
@[stacks 08ND "precomposed arbitrary-realization homotopy at the source"]
theorem precompose.realization.hom_inv_id
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) :
    Homotopic
      ((precompose.realization adj hX).hom ≫
        precompose.realization.inverse adj hX)
      (𝟙 (precompose.realization adj hX).left) := sorry

/-- The transported inverse of a precomposed arbitrary realization followed by its
augmentation is homotopic to the identity. -/
@[stacks 08ND "precomposed arbitrary-realization homotopy at the target"]
theorem precompose.realization.inv_hom_id
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) :
    Homotopic
      (precompose.realization.inverse adj hX ≫
        (precompose.realization adj hX).hom)
      (𝟙 ((const (S ⥤ A)).obj U)) := sorry

/-- The structured homotopy equivalence obtained by precomposing any realization with the
left adjoint. -/
@[stacks 08ND "structured precomposed arbitrary realization equivalence"]
noncomputable def precompose.realization.homotopyEquiv
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) :
    HomotopyEquiv (precompose.realization adj hX).left
      ((const (S ⥤ A)).obj U) :=
  (precompose.realization.extraDegeneracy adj hX).simplicialHomotopyEquiv

/-- The forward map of the precomposed arbitrary-realization equivalence is its
augmentation. -/
@[simp, stacks 08ND "forward map of the precomposed arbitrary-realization equivalence"]
theorem precompose.realization.homotopyEquiv.hom
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) :
    (precompose.realization.homotopyEquiv adj hX).hom =
      (precompose.realization adj hX).hom := sorry

/-- The inverse map of the precomposed arbitrary-realization equivalence is the transported
unit-induced inverse. -/
@[simp, stacks 08ND "inverse map of the precomposed arbitrary-realization equivalence"]
theorem precompose.realization.homotopyEquiv.inv
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) :
    (precompose.realization.homotopyEquiv adj hX).inv =
      precompose.realization.inverse adj hX := sorry

/-- Postcomposition by the right adjoint contracts the augmentation of any realization of the
adjunction's iterated-comonad data. -/
@[stacks 08ND "postcomposed arbitrary realization is a homotopy equivalence"]
theorem postcompose.realization.isHomotopyEquivalence
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) :
    IsHomotopyEquivalence (postcompose.realization adj hX).hom := sorry

/-- Precomposition by the left adjoint contracts the augmentation of any realization of the
adjunction's iterated-comonad data. -/
@[stacks 08ND "precomposed arbitrary realization is a homotopy equivalence"]
theorem precompose.realization.isHomotopyEquivalence
    (adj : U ⊣ V) {X : SimplicialObject (A ⥤ A)}
    (hX : adj.toComonad.Realizes X) :
    IsHomotopyEquivalence (precompose.realization adj hX).hom := sorry

end CategoryTheory.Adjunction.SimplicialResolution
