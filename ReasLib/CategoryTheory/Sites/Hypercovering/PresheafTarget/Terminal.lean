module

public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.LocalHypercover
public import ReasLib.CategoryTheory.Sites.Presheaf.Terminal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hypercoverings of the terminal presheaf

This leaf owns the canonical terminal augmentation and the specialization of a presheaf-target
hypercovering to the terminal presheaf. No sheafification hypothesis is needed for this data.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

namespace HypercoveringOf

/-- The canonical augmentation of a simplicial semi-representable family to the terminal
presheaf. -/
def terminalAugmentation (L : SimplicialObject (SR(C))) :
    hypercoveringPresheaf L ⟶
      (SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj (Presheaf.terminal C) :=
  ((hypercoveringPresheaf L).augmentOfIsTerminal (Presheaf.terminalIsTerminal C)).hom

/-- The terminal augmentation sends every section to the unique element of `PUnit`. -/
@[simp] theorem terminalAugmentation_app_apply
    (L : SimplicialObject (SR(C))) (Δ : SimplexCategoryᵒᵖ)
    (X : Cᵒᵖ) (x : ((hypercoveringPresheaf L).obj Δ).obj X) :
    ((terminalAugmentation L).app Δ).app X x = PUnit.unit := sorry

/-- Definition 25.6.1 (2): a site-level hypercovering is a hypercovering of the terminal
presheaf. -/
@[stacks 09VU "hypercovering of a site"]
abbrev Terminal (J : GrothendieckTopology C) :=
  HypercoveringOf.{w} J (Presheaf.terminal C)

namespace Terminal

variable (J : GrothendieckTopology C)

/-- The degree-`0` local-surjectivity condition for a site-level hypercovering. -/
abbrev ZeroLocallySurjective (simplicial : SimplicialObject (SR(C))) : Prop :=
  HypercoveringOf.ZeroLocallySurjective J simplicial (terminalAugmentation simplicial)

/-- The degree-`1` local-surjectivity condition for a site-level hypercovering. -/
abbrev OneLocallySurjective (simplicial : SimplicialObject (SR(C))) : Prop :=
  HypercoveringOf.OneLocallySurjective J simplicial (terminalAugmentation simplicial)

/-- The higher matching-map local-surjectivity condition for a site-level hypercovering. -/
abbrev HigherLocallySurjective
    (simplicial : SimplicialObject (SR(C))) (n : ℕ) : Prop :=
  HypercoveringOf.HigherLocallySurjective J simplicial n

/-- Build a site-level hypercovering from a simplicial semi-representable family and its local
matching-map conditions. -/
def ofSimplicial
    (simplicial : SimplicialObject (SR(C)))
    (zero_locallySurjective : ZeroLocallySurjective J simplicial)
    (one_locallySurjective : OneLocallySurjective J simplicial)
    (higher_locallySurjective :
      ∀ n : ℕ, HigherLocallySurjective J simplicial (n + 1)) :
    HypercoveringOf.Terminal J where
  simplicial := simplicial
  augmentation := terminalAugmentation simplicial
  isLocalHypercover :=
    SimplicialObject.Augmented.IsLocalHypercover.of_zero_one_higher
      zero_locallySurjective one_locallySurjective higher_locallySurjective

/-- `ofSimplicial` has the supplied underlying simplicial object. -/
@[simp] theorem ofSimplicial_simplicial
    (simplicial : SimplicialObject (SR(C)))
    (zero_locallySurjective : ZeroLocallySurjective J simplicial)
    (one_locallySurjective : OneLocallySurjective J simplicial)
    (higher_locallySurjective :
      ∀ n : ℕ, HigherLocallySurjective J simplicial (n + 1)) :
    (ofSimplicial J simplicial zero_locallySurjective one_locallySurjective
      higher_locallySurjective).simplicial = simplicial := sorry

/-- `ofSimplicial` stores the canonical terminal augmentation. -/
@[simp] theorem ofSimplicial_augmentation
    (simplicial : SimplicialObject (SR(C)))
    (zero_locallySurjective : ZeroLocallySurjective J simplicial)
    (one_locallySurjective : OneLocallySurjective J simplicial)
    (higher_locallySurjective :
      ∀ n : ℕ, HigherLocallySurjective J simplicial (n + 1)) :
    (ofSimplicial J simplicial zero_locallySurjective one_locallySurjective
      higher_locallySurjective).augmentation = terminalAugmentation simplicial := sorry

/-- `ofSimplicial` stores the supplied degree-`0` local-surjectivity witness. -/
@[simp] theorem ofSimplicial_zero_locallySurjective
    (simplicial : SimplicialObject (SR(C)))
    (zero_locallySurjective : ZeroLocallySurjective J simplicial)
    (one_locallySurjective : OneLocallySurjective J simplicial)
    (higher_locallySurjective :
      ∀ n : ℕ, HigherLocallySurjective J simplicial (n + 1)) :
    (ofSimplicial J simplicial zero_locallySurjective one_locallySurjective
      higher_locallySurjective).zero_locallySurjective = zero_locallySurjective := sorry

/-- `ofSimplicial` stores the supplied degree-`1` local-surjectivity witness. -/
@[simp] theorem ofSimplicial_one_locallySurjective
    (simplicial : SimplicialObject (SR(C)))
    (zero_locallySurjective : ZeroLocallySurjective J simplicial)
    (one_locallySurjective : OneLocallySurjective J simplicial)
    (higher_locallySurjective :
      ∀ n : ℕ, HigherLocallySurjective J simplicial (n + 1)) :
    (ofSimplicial J simplicial zero_locallySurjective one_locallySurjective
      higher_locallySurjective).one_locallySurjective = one_locallySurjective := sorry

/-- `ofSimplicial` stores the supplied higher matching-map witnesses. -/
@[simp] theorem ofSimplicial_higher_locallySurjective
    (simplicial : SimplicialObject (SR(C)))
    (zero_locallySurjective : ZeroLocallySurjective J simplicial)
    (one_locallySurjective : OneLocallySurjective J simplicial)
    (higher_locallySurjective :
      ∀ n : ℕ, HigherLocallySurjective J simplicial (n + 1))
    (n : ℕ) :
    (ofSimplicial J simplicial zero_locallySurjective one_locallySurjective
      higher_locallySurjective).isLocalHypercover.higher n =
        higher_locallySurjective n := sorry

end Terminal

end HypercoveringOf

end CategoryTheory
