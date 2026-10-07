module

public import ReasLib.CategoryTheory.Sites.QuasiCompact.Basis.Presentation
public import ReasLib.Topology.Opens.Basis
public import ReasLib.Topology.Sheaf.Notation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite presentations of set-valued sheaves on topological spaces

This file specializes the site-level finite-presentation API to the canonical site of opens.
The basis-relative property remains the primary owner; compact-open presentations are its
standard topological specialization.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf.BasisPresentation

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]

/-- A set-valued sheaf has a finite presentation relative to `B` when it is a coequalizer of
two maps between finite coproducts of sheafified representables associated with objects of `B`. -/
@[stacks 0CAJ "finite basis presentation"]
abbrev IsFinite (B : Set (Opens X)) :
    ObjectProperty (X.Sheaf (Type u)) :=
  CategoryTheory.GrothendieckTopology.Basis.finiteSheafPresentation
    (Opens.grothendieckTopology X) B

/-- Lemma 17.19.2 (0CAI): if `B` is a basis of compact opens, every set-valued sheaf is a
filtered colimit of sheaves with finite `B`-presentations. -/
@[stacks 0CAI]
theorem ind {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hcompact : ∀ U, U ∈ B → IsCompact (U : Set X))
    (F : X.Sheaf (Type u)) :
    (IsFinite B).ind F := sorry

end TopCat.Sheaf.BasisPresentation

namespace TopCat.Sheaf.CompactOpenPresentation

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]

/-- A set-valued sheaf has a finite compact-open presentation when it has a finite presentation
relative to the compact open subsets. -/
@[stacks 0CAK "compact-open presentation hypothesis"]
abbrev IsFinite : ObjectProperty (X.Sheaf (Type u)) :=
  BasisPresentation.IsFinite { U : Opens X | IsCompact (U : Set X) }

end TopCat.Sheaf.CompactOpenPresentation

end

end
