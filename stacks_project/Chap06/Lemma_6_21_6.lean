module

public import ReasLib.Topology.Sheaves.Pullback.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat

universe u

section

variable {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

namespace TopCat.Sheaf

/- Lemma 6.21.6 (1): pullback of sheaves of sets along `f ≫ g` is canonically isomorphic to
pullback along `g` followed by pullback along `f`. -/
@[stacks 008I "pullback composition for sheaves"]
#check
  (pullbackComp (A := Type u) f g :
    pullback (Type u) g ⋙ pullback (Type u) f ≅ pullback (Type u) (f ≫ g))

end TopCat.Sheaf

namespace TopCat.Presheaf

/- Lemma 6.21.6 (2): pullback of presheaves of sets along `f ≫ g` is canonically isomorphic to
pullback along `g` followed by pullback along `f`. -/
@[stacks 008I "pullback composition for presheaves"]
#check
  (pullbackComp (C := Type u) f g :
    pullback (Type u) g ⋙ pullback (Type u) f ≅ pullback (Type u) (f ≫ g))

end TopCat.Presheaf

end
