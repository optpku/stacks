/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.QuasiIso
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functorial K-flat resolutions

This leaf owns a selected functorial K-flat replacement as explicit data.  It is intentionally
not a typeclass: functorial resolutions need not be canonical, and downstream functors must not
be selected from the proposition that objectwise resolutions merely exist.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v u

namespace CategoryTheory.HomotopyCategory.KFlat

variable (C : Type u) [Category.{v} C] [Preadditive C]
variable [MonoidalCategory C] [MonoidalPreadditive C] [CategoryWithHomology C]

/-- Stacks 0FPB: a functorial K-flat resolution selects a K-flat replacement of every homotopy
object and a natural quasi-isomorphism from the replacement to the original object. -/
@[stacks 0FPB "functorial K-flat resolutions"]
structure ResolutionFunctor where
  /-- The selected functor from homotopy objects to K-flat homotopy objects. -/
  toFunctor : HomotopyCategory C (up ℤ) ⥤ KFlat C
  /-- The natural comparison from each selected K-flat replacement to its source object. -/
  counit : toFunctor ⋙ (kFlat C).ι ⟶ 𝟭 (HomotopyCategory C (up ℤ))
  /-- Every component of the comparison is a quasi-isomorphism. -/
  quasiIso_app (K : HomotopyCategory C (up ℤ)) :
    HomotopyCategory.quasiIso C (up ℤ) (counit.app K)

namespace ResolutionFunctor

/-- The selected K-flat replacement of a homotopy object. -/
noncomputable abbrev obj (P : ResolutionFunctor C) (K : HomotopyCategory C (up ℤ)) :
    KFlat C :=
  P.toFunctor.obj K

/-- The selected replacement viewed in the ambient homotopy category. -/
noncomputable abbrev ambient (P : ResolutionFunctor C) :
    HomotopyCategory C (up ℤ) ⥤ HomotopyCategory C (up ℤ) :=
  P.toFunctor ⋙ (kFlat C).ι

/-- The comparison from a selected K-flat replacement to its source object. -/
noncomputable abbrev counitApp (P : ResolutionFunctor C)
    (K : HomotopyCategory C (up ℤ)) :
    P.ambient.obj K ⟶ K :=
  P.counit.app K

/-- A functorial K-flat resolution supplies the existing objectwise K-flat resolution
condition. This direction forgets data and therefore remains a proposition-level bridge. -/
@[stacks 0FPB "functorial resolutions imply K-flat resolutions"]
theorem hasResolutions (P : ResolutionFunctor C) : HasResolutions C := sorry

/-- A functorial K-flat replacement carries ambient quasi-isomorphisms to restricted
quasi-isomorphisms between K-flat objects. -/
@[stacks 0FPB "functorial K-flat replacement preserves quasi-isomorphisms"]
theorem map_quasiIso (P : ResolutionFunctor C) {K L : HomotopyCategory C (up ℤ)}
    (f : K ⟶ L) (hf : HomotopyCategory.quasiIso C (up ℤ) f) :
    quasiIso (C := C) (P.toFunctor.map f) := sorry

end ResolutionFunctor

end CategoryTheory.HomotopyCategory.KFlat
