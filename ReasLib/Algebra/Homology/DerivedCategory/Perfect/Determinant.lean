/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Determinant.CanonicalElement
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Subcategory
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
public import ReasLib.RingTheory.PicardGroup.Invertible
import Mathlib.Tactic.CrossRefAttribute

/-!
# Determinants of perfect complexes with Tor-amplitude in `[-1, 0]`

The determinant line, its functoriality, and the canonical rank-zero element form one coherent
choice. They are therefore bundled in `Determinant`; the existence theorem is a proposition, so
the library does not install an arbitrary representative-dependent choice as global data.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.ObjectProperty

universe u

namespace CategoryTheory.PerfectDerived

/-- The full subcategory of perfect derived modules whose Tor-amplitude is contained in
`[-1, 0]`.  This is the intrinsic domain of the two-term determinant construction. -/
@[stacks 0FJM "perfect complexes of Tor-amplitude [-1, 0]"]
abbrev TorNegOneZero (R : Type u) [CommRing R] : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun K : PerfectDerived R =>
      DerivedCategory.HasTorAmplitudeIn (R := R) K.obj (-1) 0)

namespace TorNegOneZero

variable (R : Type u) [CommRing R]

/-- A coherent determinant construction on perfect complexes of Tor-amplitude `[-1, 0]`.

The groupoid-valued functor is concrete data.  Its codomain records invertibility by construction;
representative comparison, rank zero, and canonical-element compatibility are laws attached to
that same data, rather than separate noncanonical choices. -/
@[stacks 0FJM "coherent determinant construction"]
structure Determinant where
  /-- The determinant functor, landing directly in the groupoid of invertible modules. -/
  det : Core (PerfectDerived.TorNegOneZero R) ⥤ ModuleCat.Invertible.Core R
  /-- The intrinsic rank-zero predicate on the derived object. -/
  isRankZero : PerfectDerived.TorNegOneZero R → Prop
  /-- Rank zero is invariant under isomorphism, in the direction used by canonical elements. -/
  rankZero_of_iso :
    ∀ {K L : PerfectDerived.TorNegOneZero R},
      CategoryTheory.Iso K L → isRankZero L → isRankZero K
  /-- The canonical element in the determinant line of a rank-zero object. -/
  canonicalElement :
    ∀ (K : PerfectDerived.TorNegOneZero R), isRankZero K → (det.obj ⟨K⟩).of.obj
  /-- The determinant functor carries canonical elements through isomorphisms. -/
  map_canonicalElement :
    ∀ {K L : PerfectDerived.TorNegOneZero R}
      (a : CategoryTheory.Iso K L) (hL : isRankZero L),
      (det.map ⟨a⟩).iso.hom.hom
          (canonicalElement K (rankZero_of_iso a hL)) =
        canonicalElement L hL
  /-- Comparison with every two-term finite-projective representative. -/
  representativeIso :
    ∀ (K : PerfectDerived.TorNegOneZero R)
      (P : CochainComplex (ModuleCat R) Int)
      (_ : K.obj.obj ≅ DerivedCategory.Q.obj P)
      [P.IsStrictlyGE (-1)] [P.IsStrictlyLE 0]
      [Module.Finite R (P.X (-1))] [Module.Projective R (P.X (-1))]
      [Module.Finite R (P.X 0)] [Module.Projective R (P.X 0)],
        (det.obj ⟨K⟩).of.obj ≅ ModuleCat.of R (CochainComplex.Determinant.line P)
  /-- A representative computes the intrinsic rank-zero predicate. -/
  rankZero_iff :
    ∀ (K : PerfectDerived.TorNegOneZero R)
      (P : CochainComplex (ModuleCat R) Int)
      (_ : K.obj.obj ≅ DerivedCategory.Q.obj P)
      [P.IsStrictlyGE (-1)] [P.IsStrictlyLE 0]
      [Module.Finite R (P.X (-1))] [Module.Projective R (P.X (-1))]
      [Module.Finite R (P.X 0)] [Module.Projective R (P.X 0)],
        isRankZero K ↔ CochainComplex.Determinant.IsRankZero P
  /-- The representative comparison sends the intrinsic canonical element to the concrete
  two-term canonical element. -/
  representativeIso_hom_canonicalElement :
    ∀ (K : PerfectDerived.TorNegOneZero R) (hK : isRankZero K)
      (P : CochainComplex (ModuleCat R) Int)
      (e : K.obj.obj ≅ DerivedCategory.Q.obj P)
      [P.IsStrictlyGE (-1)] [P.IsStrictlyLE 0]
      [Module.Finite R (P.X (-1))] [Module.Projective R (P.X (-1))]
      [Module.Finite R (P.X 0)] [Module.Projective R (P.X 0)],
        (representativeIso K P e).hom (canonicalElement K hK) =
          CochainComplex.Determinant.canonical P ((rankZero_iff K P e).1 hK)

namespace Determinant

/-- The underlying determinant line selected for an object.  This is a projection from `det`, not
a second choice of module. -/
@[stacks 0FJM "determinant line of a perfect derived object"]
def line (D : Determinant R) (K : PerfectDerived.TorNegOneZero R) : ModuleCat R :=
  (D.det.obj ⟨K⟩).of.obj

end Determinant

/-- A coherent determinant construction exists for perfect complexes of Tor-amplitude
`[-1, 0]`. -/
@[stacks 0FJM "Lemma 15.123.4: determinant functor and canonical element"]
theorem nonemptyDeterminant : Nonempty (Determinant R) := sorry
-- Proof strategy: choose two-term finite-projective representatives for objects
-- of Tor-amplitude `[-1, 0]`, compare representatives through admissible common
-- refinements, and use `map_comp`, `equiv_eq_of_perturbation`, and
-- `equiv_canonical` to prove functoriality and representative independence.

end TorNegOneZero

end CategoryTheory.PerfectDerived

end
