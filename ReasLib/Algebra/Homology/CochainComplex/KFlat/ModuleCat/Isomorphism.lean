module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.Relative.Isomorphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism Transport for K-Flat Complexes over a Ring

This file specializes relative isomorphism transport to the universe-polymorphic tensor
bifunctor defining K-flatness over a commutative ring.
@stack 06XZ
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CochainComplex

variable {R : Type u} [CommRing R]

namespace IsKFlatOver

/-- K-flatness over the ground ring transports along an isomorphism of module-valued cochain
complexes. -/
theorem of_iso {K L : CochainComplex (ModuleCat.{v} R) ℤ}
    (hK : K.IsKFlatOver) (e : K ≅ L) : L.IsKFlatOver := sorry

/-- Isomorphic module-valued cochain complexes are simultaneously K-flat over the ground
ring. -/
@[stacks 06XZ "isomorphism invariance of K-flatness over a ring"]
theorem iff_of_iso {K L : CochainComplex (ModuleCat.{v} R) ℤ} (e : K ≅ L) :
    K.IsKFlatOver ↔ L.IsKFlatOver := sorry

end IsKFlatOver

end CochainComplex
