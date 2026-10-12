/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic.Computations

/-!
# Naturality API for explicit pseudo-pullbacks

This leaf records the coherent public reconstruction laws of the explicit pseudo-pullback:
base-identification naturality, the comparison square, and extensionality. These statements are
kept separate from construction data so downstream proofs can import exactly the coherence layer
they use.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open BasedNatIso
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback
open scoped Bicategory BasedFunctor

universe u v w vB uX vX uY vY uS vS

namespace CategoryTheory

open Bicategory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}
variable {F : X ⥤ᵇ S} {G : Y ⥤ᵇ S}

namespace PseudoPullback

/-- The stored first-component base identification is natural in a pseudo-pullback morphism.

This is the direct `IsHomLift.fac'` form for the first component. It belongs to the explicit
pseudo-pullback owner, so applications which only need base transport do not have to import the
categorical-pullback comparison layer. -/
@[reassoc]
theorem fstBaseIso.naturality {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    X.p.map (fstMap φ) ≫ (fstBaseIso Q).hom =
      (fstBaseIso P).hom ≫ baseMap φ := sorry

/-- The inverse stored first-component base identification is natural in a pseudo-pullback
morphism. -/
@[reassoc]
theorem fstBaseIso.invNaturality {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    baseMap φ ≫ (fstBaseIso Q).inv =
      (fstBaseIso P).inv ≫ X.p.map (fstMap φ) := sorry

/-- The stored second-component base identification is natural in a pseudo-pullback morphism.

This is the direct `IsHomLift.fac'` form for the second component. It belongs to the explicit
pseudo-pullback owner, so applications which only need base transport do not have to import the
categorical-pullback comparison layer. -/
@[reassoc]
theorem sndBaseIso.naturality {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    Y.p.map (sndMap φ) ≫ (sndBaseIso Q).hom =
      (sndBaseIso P).hom ≫ baseMap φ := sorry

/-- The inverse stored second-component base identification is natural in a pseudo-pullback
morphism. -/
@[reassoc]
theorem sndBaseIso.invNaturality {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    baseMap φ ≫ (sndBaseIso Q).inv =
      (sndBaseIso P).inv ≫ Y.p.map (sndMap φ) := sorry

/-- The component maps of a pseudo-pullback morphism form its comparison square. -/
theorem comm {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    CommSq (F.toFunctor.map (fstMap φ)) (comparison P) (comparison Q)
      (G.toFunctor.map (sndMap φ)) := sorry
-- Proof strategy: extract the comm field from the implementation morphism.

/-- The component maps supplied to the explicit constructor satisfy its requested comparison
square. -/
theorem Hom.mk.comm
    {P Q : (PseudoPullback F G).obj}
    (base : baseObj P ⟶ baseObj Q)
    (fst : fstObj P ⟶ fstObj Q) (fst_isHomLift : X.p.IsHomLift base fst)
    (snd : sndObj P ⟶ sndObj Q) (snd_isHomLift : Y.p.IsHomLift base snd)
    (w : CommSq (F.toFunctor.map fst) (PseudoPullback.comparison P)
      (PseudoPullback.comparison Q)
      (G.toFunctor.map snd)) :
    CommSq
      (F.toFunctor.map
        (PseudoPullback.fstMap (PseudoPullback.Hom.mk
          base fst fst_isHomLift snd snd_isHomLift w)))
      (PseudoPullback.comparison P)
      (PseudoPullback.comparison Q)
      (G.toFunctor.map
        (PseudoPullback.sndMap (PseudoPullback.Hom.mk
          base fst fst_isHomLift snd snd_isHomLift w))) := sorry

/-- The component maps supplied to the typeclass-driven constructor satisfy its requested
comparison square. -/
theorem homMk.comm
    {P Q : (PseudoPullback F G).obj}
    (base : baseObj P ⟶ baseObj Q)
    (fst : fstObj P ⟶ fstObj Q) [X.p.IsHomLift base fst]
    (snd : sndObj P ⟶ sndObj Q) [Y.p.IsHomLift base snd]
    (w : CommSq (F.toFunctor.map fst) (PseudoPullback.comparison P)
      (PseudoPullback.comparison Q)
      (G.toFunctor.map snd)) :
    CommSq
      (F.toFunctor.map (PseudoPullback.fstMap (PseudoPullback.homMk base fst snd w)))
      (PseudoPullback.comparison P) (PseudoPullback.comparison Q)
      (G.toFunctor.map (PseudoPullback.sndMap (PseudoPullback.homMk base fst snd w))) := sorry

/-- Reconstructing a pseudo-pullback morphism from its public base map, component maps, lifting
witnesses, and comparison square is the identity. This is the public eta rule for `homMk`. -/
@[simp]
theorem homMk.eta {P Q : (PseudoPullback F G).obj} (φ : P ⟶ Q) :
    PseudoPullback.homMk (PseudoPullback.baseMap φ) (PseudoPullback.fstMap φ)
      (PseudoPullback.sndMap φ) (PseudoPullback.comm φ) = φ := sorry

/-- Pseudo-pullback morphisms are determined by their two component maps. -/
@[ext]
theorem hom_ext {P Q : (PseudoPullback F G).obj} (φ ψ : P ⟶ Q)
    (hfst : fstMap φ = fstMap ψ)
    (hsnd : sndMap φ = sndMap ψ) : φ = ψ := sorry
-- Proof strategy: coerce to the private morphism carrier and apply its extensionality theorem.

end PseudoPullback
end BasedCategory
end CategoryTheory
