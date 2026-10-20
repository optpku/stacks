module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.InverseSystem.LeftSystem.Derived.HomOver
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.InverseSystem.Interleaving
import Mathlib.Tactic.CrossRefAttribute

/-!
# Interleavings of ordinary left DG-module systems in derived stage categories

Two ordinary left DG-module systems are interleaved when their derived stages admit alternating
cross-index morphisms along a common strictly increasing reindexing, and consecutive maps recover
the canonical derived transitions.
-/

@[expose] public section

noncomputable section

universe u x v

open CategoryTheory Opposite
open DifferentialGradedModule.InverseSystem.Derived.Left

namespace DifferentialGradedModule.InverseSystem.LeftSystem.Derived

variable {R : Type u} [CommRing R]

/-- Witness data for an interleaving of the derived stages of two ordinary left DG-module
systems, normalized by `reindex 0 = 0`. -/
@[stacks 0GZI "interleavings of ordinary left DG-module systems"]
structure Interleaving
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (N N' : LeftSystem.{u, x, v} A) where
  /-- The common order-preserving reindexing of the two systems. -/
  reindex : ℕ →o ℕ
  /-- The common reindexing is strictly increasing. -/
  strictMono : StrictMono reindex
  /-- The zero-based normalization corresponding to the source convention `n₀ = 1`. -/
  reindex_zero : reindex 0 = 0
  /-- The derived cross-index morphism from the next even stage of `N` to the intervening odd
  stage of `N'`. -/
  evenToOdd (i : ℕ) :
    HomOver A N N' (oddEvenLE reindex i)
  /-- The derived cross-index morphism from an odd stage of `N'` to the preceding even stage of
  `N`. -/
  oddToEven (i : ℕ) :
    HomOver A N' N (evenOddLE reindex i)
  /-- Two consecutive alternating morphisms recover the canonical derived transition of `N`. -/
  evenComp (i : ℕ) :
    HomOver.comp (evenToOdd i) (oddToEven i) =
      HomOver.transition A N (evenSpanLE reindex i)
  /-- Two consecutive alternating morphisms recover the canonical derived transition of
  `N'`. -/
  oddComp (i : ℕ) :
    HomOver.comp (oddToEven (i + 1)) (evenToOdd i) =
      HomOver.transition A N' (oddSpanLE reindex i)

namespace Interleaving

variable {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}
variable {N N' : LeftSystem.{u, x, v} A}

/-- Localizing the two maps around an even stage recovers the corresponding global
transition. -/
theorem toGlobal_evenComp (z : Interleaving A N N') (i : ℕ) :
    DifferentialGradedModule.InverseSystem.Derived.Left.HomOver.comp
        (HomOver.toGlobal (z.evenToOdd i))
        (HomOver.toGlobal (z.oddToEven i)) =
      DifferentialGradedModule.InverseSystem.Derived.Left.HomOver.transition A
        ((DifferentialGradedModule.InverseSystem.Derived.Left.Q A).obj N)
        (evenSpanLE z.reindex i) := sorry

/-- Localizing the two maps around an odd stage recovers the corresponding global
transition. -/
theorem toGlobal_oddComp (z : Interleaving A N N') (i : ℕ) :
    DifferentialGradedModule.InverseSystem.Derived.Left.HomOver.comp
        (HomOver.toGlobal (z.oddToEven (i + 1)))
        (HomOver.toGlobal (z.evenToOdd i)) =
      DifferentialGradedModule.InverseSystem.Derived.Left.HomOver.transition A
        ((DifferentialGradedModule.InverseSystem.Derived.Left.Q A).obj N')
        (oddSpanLE z.reindex i) := sorry

/-- Localize an interleaving of ordinary left module systems to an interleaving in the
canonical global left derived category. -/
@[stacks 0GZI "localization of interleaved left module systems"]
noncomputable def toGlobal (z : Interleaving A N N') :
    DifferentialGradedModule.InverseSystem.Derived.Left.Interleaving A
      ((DifferentialGradedModule.InverseSystem.Derived.Left.Q A).obj N)
      ((DifferentialGradedModule.InverseSystem.Derived.Left.Q A).obj N') where
  reindex := z.reindex
  strictMono := z.strictMono
  evenToOdd i := HomOver.toGlobal (z.evenToOdd i)
  oddToEven i := HomOver.toGlobal (z.oddToEven i)
  evenComp := toGlobal_evenComp z
  oddComp := toGlobal_oddComp z

/-- Localization preserves the reindexing of an ordinary left-system interleaving. -/
@[simp]
theorem toGlobal_reindex (z : Interleaving A N N') :
    z.toGlobal.reindex = z.reindex := sorry

/-- The localized even-to-odd component is the localization of the source-shaped component. -/
@[simp]
theorem toGlobal_evenToOdd (z : Interleaving A N N') (i : ℕ) :
    z.toGlobal.evenToOdd i = HomOver.toGlobal (z.evenToOdd i) := sorry

/-- The localized odd-to-even component is the localization of the source-shaped component. -/
@[simp]
theorem toGlobal_oddToEven (z : Interleaving A N N') (i : ℕ) :
    z.toGlobal.oddToEven i = HomOver.toGlobal (z.oddToEven i) := sorry

/-- The source normalization remains available after passing to the global interleaving. -/
@[simp]
theorem toGlobal_reindex_zero (z : Interleaving A N N') :
    z.toGlobal.reindex 0 = 0 := sorry

end Interleaving

/-- Lemma 24.35.2 (Stacks 0GZI): two ordinary left DG-module systems are derived
pro-isomorphic when their derived stages admit an interleaving. -/
@[stacks 0GZI "derived pro-isomorphism of ordinary left DG-module systems"]
def AreProIsomorphic
    {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}
    (N N' : LeftSystem.{u, x, v} A) : Prop :=
  Nonempty (Interleaving A N N')

namespace AreProIsomorphic

variable {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}
variable {N N' : LeftSystem.{u, x, v} A}

/-- Every ordinary left module system is derived pro-isomorphic to itself. -/
@[refl]
theorem refl (N : LeftSystem.{u, x, v} A) :
    AreProIsomorphic N N := sorry

/-- Derived pro-isomorphism of ordinary left module systems is symmetric. -/
@[symm]
theorem symm (h : AreProIsomorphic N N') :
    AreProIsomorphic N' N := sorry

/-- Derived pro-isomorphisms of ordinary left module systems compose. -/
@[trans]
theorem trans {N'' : LeftSystem.{u, x, v} A}
    (h : AreProIsomorphic N N') (h' : AreProIsomorphic N' N'') :
    AreProIsomorphic N N'' := sorry

/-- A derived pro-isomorphism of ordinary left systems yields an interleaving of their images
in the canonical global derived category. -/
theorem toGlobal (h : AreProIsomorphic N N') :
    Nonempty
      (DifferentialGradedModule.InverseSystem.Derived.Left.Interleaving A
        ((DifferentialGradedModule.InverseSystem.Derived.Left.Q A).obj N)
        ((DifferentialGradedModule.InverseSystem.Derived.Left.Q A).obj N')) := sorry

end AreProIsomorphic

end DifferentialGradedModule.InverseSystem.LeftSystem.Derived
