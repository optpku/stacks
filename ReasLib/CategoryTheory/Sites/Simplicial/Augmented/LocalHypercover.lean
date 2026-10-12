/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.Over
public import ReasLib.CategoryTheory.MorphismProperty.Hypercovering
public import ReasLib.CategoryTheory.Sites.Presheaf.LocallySurjective
public import ReasLib.CategoryTheory.Sites.Simplicial.Augmented
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local hypercovers of presheaves

This leaf owns the topology-relative local-hypercover predicate for an arbitrary augmented
simplicial presheaf. It is independent of any representability condition and is therefore the
common input to both generic homology results and concrete hypercovering constructions.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.Augmented

open Opposite
open scoped Simplicial

variable {C : Type u} [Category.{v} C]

/-- Definition 25.6.1 (Tag 09VU), in its representability-free form: an augmented simplicial
presheaf is a local hypercover when its augmentation, its degree-one matching map, and every
higher matching map are locally surjective. -/
@[stacks 09VU "local hypercover condition"]
abbrev IsLocalHypercover
    (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) : Prop :=
  MorphismProperty.Hypercovering (Presheaf.locallySurjective J) A.toOver

namespace IsLocalHypercover

/-- The generic degree-zero condition is the local surjectivity of the
degree-zero augmentation map. -/
theorem zero_iff
    (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) :
    Presheaf.locallySurjective J ((A.toOver.obj (op ⦋0⦌)).hom) ↔
      Presheaf.IsLocallySurjective J A.zeroMap := sorry

/-- The generic zeroth matching condition is the local surjectivity of the
degree-one matching map. -/
theorem one_iff
    (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) :
    Presheaf.locallySurjective J
        ((SimplicialObject.matchingMap A.toOver 0).left) ↔
      Presheaf.IsLocallySurjective J A.oneMap := sorry

/-- The generic matching condition in level `n + 1` is the local
surjectivity of the corresponding higher simplicial-presheaf matching map. -/
theorem higher_iff
    (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) (n : ℕ) :
    Presheaf.locallySurjective J
        ((SimplicialObject.matchingMap A.toOver (n + 1)).left) ↔
      Presheaf.IsLocallySurjective J
        (SimplicialObject.matchingMap A.left (n + 1)) := sorry

/-- The degree-zero augmentation of a local hypercover is locally surjective. -/
theorem zero {J : GrothendieckTopology C}
    {A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)}
    (hA : A.IsLocalHypercover J) :
    Presheaf.IsLocallySurjective J A.zeroMap := sorry

/-- The degree-one matching map of a local hypercover is locally surjective. -/
theorem one {J : GrothendieckTopology C}
    {A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)}
    (hA : A.IsLocalHypercover J) :
    Presheaf.IsLocallySurjective J A.oneMap := sorry

/-- Every higher matching map of a local hypercover is locally surjective. -/
theorem higher {J : GrothendieckTopology C}
    {A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)}
    (hA : A.IsLocalHypercover J) (n : ℕ) :
    Presheaf.IsLocallySurjective J
      (SimplicialObject.matchingMap A.left (n + 1)) := sorry

/-- The degree-zero, degree-one, and higher local-surjectivity conditions
construct a local hypercover. -/
theorem of_zero_one_higher {J : GrothendieckTopology C}
    {A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)}
    (h_zero :
      Presheaf.IsLocallySurjective J A.zeroMap)
    (h_one : Presheaf.IsLocallySurjective J A.oneMap)
    (h_higher : ∀ n : ℕ,
      Presheaf.IsLocallySurjective J
        (SimplicialObject.matchingMap A.left (n + 1))) :
    A.IsLocalHypercover J := sorry

end IsLocalHypercover

/-- The local-hypercover predicate is exactly the degree-zero, degree-one, and higher matching-map
local-surjectivity conditions. -/
theorem isLocalHypercover_iff
    (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) :
    A.IsLocalHypercover J ↔
      Presheaf.IsLocallySurjective J A.zeroMap ∧
      Presheaf.IsLocallySurjective J A.oneMap ∧
      ∀ n : ℕ,
        Presheaf.IsLocallySurjective J
          (SimplicialObject.matchingMap A.left (n + 1)) := sorry

end CategoryTheory.SimplicialObject.Augmented
