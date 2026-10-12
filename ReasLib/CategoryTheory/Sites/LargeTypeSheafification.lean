/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.TypeSheafification
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Types.Multiequalizer
public import Mathlib.CategoryTheory.UnivLE
public import Mathlib.Logic.Small.Basic

/-!
# Large-universe Type-valued sheafification

This leaf owns the Type-valued `Plus` and weak-sheafification facts whose
target universe must be enlarged to contain the site.  The smaller-universe
interface lives in `Sites.TypeSheafification`; the statements here retain the
explicit concrete `Plus` hypotheses needed before a sheafification structure
has been chosen.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w

namespace CategoryTheory.GrothendieckTopology

/-- In the Type universe enlarged to contain a site, weak sheafification
local equivalences are exactly locally bijective maps. -/
theorem largeType_WEqualsLocallyBijective
    {E : Type u} [Category.{v} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type (max w (max u v)))] :
    L.WEqualsLocallyBijective (Type (max w (max u v))) := sorry

/-- The `Plus` map is a weak equivalence after enlarging the Type universe to
contain the site.  This is the direct downstream form of the local-bijectivity
API. -/
theorem toPlus_mem_W_of_largeType
    {E : Type u} [Category.{v} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type (max w (max u v)))]
    (P : Eᵒᵖ ⥤ Type (max w (max u v))) :
    L.W (L.toPlus P) := sorry

end CategoryTheory.GrothendieckTopology
