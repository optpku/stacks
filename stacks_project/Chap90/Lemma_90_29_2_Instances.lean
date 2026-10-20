/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.ResidueChange.Properties
import StacksCheckRecall

/-!
# Preservation of deformation conditions under residue-field change
-/

@[expose] public section

open CategoryTheory Functor ArtinianLocalAlgCat

universe u v w

variable (Λ k l : Type u) [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]
variable {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)

section Predeformation

variable [IsPredeformationCategory p]

/- Lemma 90.29.2 (2): Residue-field change preserves IsPredeformationCategory. -/
@[stacks 07WA]
#check (ArtinianLocalAlgCat.residueChangeOver.instIsPredeformationCategory Λ k l p :
  IsPredeformationCategory (residueChangeOver Λ k l p))

end Predeformation

section S1

variable [IsFibered.InGroupoids p.op] [HasSchlessingerS1 p]

/- Lemma 90.29.2 (3): Residue-field change preserves HasSchlessingerS1. -/
@[stacks 07WA]
#check (ArtinianLocalAlgCat.residueChangeOver.instHasSchlessingerS1 Λ k l p :
  HasSchlessingerS1 (residueChangeOver Λ k l p))

end S1

section S2

variable [IsFibered.InGroupoids p.op] [HasSchlessingerS2 p]

/- Lemma 90.29.2 (4): Residue-field change preserves HasSchlessingerS2. -/
@[stacks 07WA]
#check (ArtinianLocalAlgCat.residueChangeOver.instHasSchlessingerS2 Λ k l p :
  HasSchlessingerS2 (residueChangeOver Λ k l p))

end S2

section RS

variable [HasRimSchlessinger p]

/- Lemma 90.29.2 (5): Residue-field change preserves HasRimSchlessinger. -/
@[stacks 07WA]
#check (ArtinianLocalAlgCat.residueChangeOver.instHasRimSchlessinger Λ k l p :
  HasRimSchlessinger (residueChangeOver Λ k l p))

end RS

#check (ArtinianLocalAlgCat.residueChangeOver.map_surjective Λ k l :
  ∀ {B B' : ArtinianLocalAlgCat Λ l} (f : B ⟶ B'),
    Function.Surjective f.hom →
      Function.Surjective ((residueChangeFunctor Λ k l).map f).hom)

#check (ArtinianLocalAlgCat.residueChangeOver.map_isPullback Λ k l :
  ∀ {A A1 A2 P : ArtinianLocalAlgCat Λ l}
    {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2},
    IsPullback π1 π2 f1 f2 →
      IsPullback ((residueChangeFunctor Λ k l).map π1)
        ((residueChangeFunctor Λ k l).map π2)
        ((residueChangeFunctor Λ k l).map f1)
        ((residueChangeFunctor Λ k l).map f2))
