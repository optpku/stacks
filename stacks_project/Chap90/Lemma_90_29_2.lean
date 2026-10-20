module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.ResidueChange.Properties
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.ResidueChange.IsoClass
import StacksCheckRecall

/-!
# Elementary properties of change of residue field

In Situation 90.29.1, fibrewise isomorphism classes commute with residue-field
reindexing, and predeformation, (S1), (S2), and (RS) pass from `p` to
`residueChangeOver p`.
-/

@[expose] public section

open CategoryTheory Functor ArtinianLocalAlgCat

universe u v w

variable (Λ k l : Type u) [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]
variable {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)

section IsoClass

variable [IsFibered.InGroupoids p.op]

/- Lemma 90.29.2 (1): Fibrewise isomorphism classes commute naturally with
residue-field change. -/
@[stacks 07WA]
#check (ArtinianLocalAlgCat.residueChangeOver.isoClassEquiv Λ k l p :
  ∀ B : ArtinianLocalAlgCat Λ l,
    isomorphismClasses.obj (Cat.of ((residueChangeOver Λ k l p).Fiber B)) ≃
      isomorphismClasses.obj (Cat.of (p.Fiber ((residueChangeFunctor Λ k l).obj B))))

#check (ArtinianLocalAlgCat.residueChangeOver.isoClassEquiv_natural Λ k l p :
  ∀ {B B' : ArtinianLocalAlgCat Λ l} (f : B ⟶ B')
    (x : isomorphismClasses.obj (Cat.of ((residueChangeOver Λ k l p).Fiber B))),
    ArtinianLocalAlgCat.residueChangeOver.isoClassEquiv Λ k l p B'
        ((fiberIsoClassFunctor (residueChangeOver Λ k l p)).map f x) =
      (fiberIsoClassFunctor p).map ((residueChangeFunctor Λ k l).map f)
        (ArtinianLocalAlgCat.residueChangeOver.isoClassEquiv Λ k l p B x))

end IsoClass

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
