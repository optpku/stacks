module

public import Mathlib.CategoryTheory.Sites.Types
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite

universe u

/- 7.15.3.1: in the singleton case of Remark 7.15.3, the equivalence of topoi
i : Sh(pt) → Sh(S) is given by i⁻¹ ℱ = ℱ(e) and
i_* E = (U ↦ Mor_Sets(U, E)), with e a singleton in the site of sets S.

The canonical owner is typeEquiv : Type u ≌ Sheaf typesGrothendieckTopology (Type u)
on the jointly-surjective type site, identifying e with PUnit. The inverse
is evaluation at op PUnit, so i⁻¹ ℱ = ℱ(PUnit), and the functor is yoneda',
so i_* E is the sheaf U ↦ (U ⟶ E). -/
@[stacks 05UW] #check typeEquiv.{u}

#check (typeEquiv.{u}.inverse :
    Sheaf typesGrothendieckTopology (Type u) ⥤ Type u)

#check (typeEquiv.{u}.functor :
    Type u ⥤ Sheaf typesGrothendieckTopology (Type u))

#check yoneda'.{u}

#check yoneda'_comp.{u}
