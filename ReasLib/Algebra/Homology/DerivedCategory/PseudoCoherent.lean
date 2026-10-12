/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.LinearAlgebra.Dimension.Finite
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pseudo-coherent complexes

This file owns pseudo-coherence predicates for complexes, derived objects, and modules over an
arbitrary ring.
@stack 064Q
-/

@[expose] public section

noncomputable section

open CategoryTheory
open ComplexShape

universe u

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

namespace DerivedCategory

/-- An object `K^•` of `D(R)` is `m`-pseudo-coherent if it admits a map
from a bounded cochain complex of finite free `R`-modules inducing isomorphisms on cohomology in
degrees `> m` and an epimorphism in degree `m`. -/
@[stacks 064Q "(1), m-pseudo-coherent derived object"]
def IsMPseudoCoherent (K : DerivedCategory (ModuleCat R)) (m : ℤ) : Prop :=
  ∃ E : CochainComplex (ModuleCat R) ℤ,
    (∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) ∧
      E.IsTermwiseFiniteFree ∧
      ∃ α : DerivedCategory.Q.obj E ⟶ K,
        (∀ i : ℤ, m < i →
          IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map α)) ∧
          Epi ((DerivedCategory.homologyFunctor (ModuleCat R) m).map α)

/-- An object `K^•` of `D(R)` is pseudo-coherent if it is represented in the derived category by
a bounded-above cochain complex of finite free `R`-modules. -/
@[stacks 064Q "(2), pseudo-coherent derived object"]
def IsPseudoCoherent (K : DerivedCategory (ModuleCat R)) : Prop :=
  ∃ E : CochainComplex (ModuleCat R) ℤ,
    (∃ b : ℤ, E.IsStrictlyLE b) ∧
      E.IsTermwiseFiniteFree ∧
      ∃ α : DerivedCategory.Q.obj E ⟶ K, IsIso α

namespace IsMPseudoCoherent

/-- An `m`-pseudo-coherent object is `n`-pseudo-coherent for every `m ≤ n`. -/
@[stacks 064Q "monotonicity of the pseudo-coherence bound"]
theorem mono {K : DerivedCategory (ModuleCat R)} {m n : ℤ}
    (hK : K.IsMPseudoCoherent m) (hmn : m ≤ n) :
    K.IsMPseudoCoherent n := sorry

/-- Transport `m`-pseudo-coherence across an isomorphism of derived module objects. -/
@[stacks 064Q "m-pseudo-coherence is invariant under isomorphism"]
theorem ofIso {K L : DerivedCategory (ModuleCat R)} (e : K ≅ L) {m : ℤ}
    (hK : K.IsMPseudoCoherent m) :
    L.IsMPseudoCoherent m := sorry

/-- `m`-pseudo-coherence of derived module objects is invariant under isomorphism. -/
@[stacks 064Q "m-pseudo-coherence is invariant under isomorphism"]
instance closedUnderIsomorphisms (m : ℤ) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun K : DerivedCategory (ModuleCat R) ↦ K.IsMPseudoCoherent m) := sorry

end IsMPseudoCoherent

namespace IsPseudoCoherent

/-- Pseudo-coherence of derived module objects is invariant under isomorphism. -/
@[stacks 064Q "pseudo-coherence is invariant under isomorphism"]
instance closedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsPseudoCoherent : ObjectProperty (DerivedCategory (ModuleCat R))) := sorry

end IsPseudoCoherent

end DerivedCategory

namespace CochainComplex

/-- A cochain complex is `m`-pseudo-coherent when its image in `D(R)` is
`m`-pseudo-coherent. -/
@[stacks 064Q "m-pseudo-coherent cochain complex"]
abbrev IsMPseudoCoherent (K : CochainComplex (ModuleCat R) ℤ) (m : ℤ) : Prop :=
  DerivedCategory.IsMPseudoCoherent (DerivedCategory.Q.obj K) m

/-- A cochain complex is pseudo-coherent when its image in `D(R)` is pseudo-coherent. -/
@[stacks 064Q "pseudo-coherent cochain complex"]
abbrev IsPseudoCoherent (K : CochainComplex (ModuleCat R) ℤ) : Prop :=
  DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj K)

end CochainComplex

namespace ModuleCat

/-- An `R`-module `M` is `m`-pseudo-coherent when the derived object `M[0]` is
`m`-pseudo-coherent. -/
@[stacks 064Q "(3), m-pseudo-coherent module"]
abbrev IsMPseudoCoherent (M : ModuleCat R) (m : ℤ) : Prop :=
  DerivedCategory.IsMPseudoCoherent (single0Functor.obj M) m

/-- An `R`-module `M` is pseudo-coherent when the derived object `M[0]` is pseudo-coherent. -/
@[stacks 064Q "(4), pseudo-coherent module"]
abbrev IsPseudoCoherent (M : ModuleCat R) : Prop :=
  DerivedCategory.IsPseudoCoherent (single0Functor.obj M)

end ModuleCat

end

end CategoryTheory
