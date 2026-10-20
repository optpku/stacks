module

public import ReasLib.Topology.Sheaves.Abelian
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat

universe u

open scoped TopCat

variable {X : TopCat.{u}}

/- Definition 6.8.1 (1): an `AddCommGrpCat`-valued presheaf is an abelian sheaf exactly when its
underlying `Type`-valued presheaf is a sheaf. -/
@[stacks 0070 "underlying presheaf of sets is a sheaf"]
#check
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) :
    ∀ F : X.Presheaf AddCommGrpCat,
      F.IsSheaf ↔ TopCat.Presheaf.IsSheaf (F ⋙ forget AddCommGrpCat))

variable (X : TopCat.{u})

/- Definition 6.8.1 (2): the category of abelian sheaves on `X`, denoted `Ab(X)` in the Stacks
Project, is the canonical sheaf owner specialized to `AddCommGrpCat`. -/
@[stacks 0070 "category of sheaves of abelian groups"]
#check (Ab(X))
