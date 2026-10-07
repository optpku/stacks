module

public import stacks_project.Chap90.Definition_90_10_1_Schlessinger
public import stacks_project.Chap90.Definition_90_16_8_RimSchlessinger
public import stacks_project.Chap90.Situation_90_29_1_Pullback

/-!
# Transfer of predeformation and Schlessinger conditions along residue-field change

Predeformation, (S1), (S2), and (RS) pass from a cofibered groupoid over
`C_{Λ, k}` to its reindexing `residueChangeOver p` over `C_{Λ, l}`.
-/

@[expose] public section

open CategoryTheory Functor

universe u v w

namespace ArtinianLocalAlgCat

variable (Λ k l : Type u) [CommRing Λ] [IsNoetherianRing Λ]
  [Field k] [Algebra Λ k] [Module.Finite Λ k]
  [Field l] [Algebra Λ l] [Module.Finite Λ l]
  [Algebra k l] [IsScalarTower Λ k l] [Module.Finite k l]

namespace residueChangeOver

/-- Residue-field change sends surjective algebra maps to surjective algebra maps. -/
theorem map_surjective {B B' : ArtinianLocalAlgCat Λ l} (f : B ⟶ B')
    (hf : Function.Surjective f.hom) :
    Function.Surjective ((residueChangeFunctor Λ k l).map f).hom :=
  sorry

/-- Residue-field change preserves pullback squares in `ArtinianLocalAlgCat`. -/
theorem map_isPullback {A A1 A2 P : ArtinianLocalAlgCat Λ l}
    {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {π1 : P ⟶ A1} {π2 : P ⟶ A2}
    (h : IsPullback π1 π2 f1 f2) :
    IsPullback ((residueChangeFunctor Λ k l).map π1)
      ((residueChangeFunctor Λ k l).map π2)
      ((residueChangeFunctor Λ k l).map f1)
      ((residueChangeFunctor Λ k l).map f2) :=
  sorry

variable {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)

/-- If `p` is a predeformation category over `C_{Λ, k}`, then so is
`residueChangeOver p` over `C_{Λ, l}`. -/
instance instIsPredeformationCategory [IsPredeformationCategory p] :
    IsPredeformationCategory (residueChangeOver Λ k l p) :=
  sorry

/-- If `p` satisfies Schlessinger's condition (S1), then so does
`residueChangeOver p`. -/
instance instHasSchlessingerS1 [IsFibered.InGroupoids p.op] [HasSchlessingerS1 p] :
    HasSchlessingerS1 (residueChangeOver Λ k l p) :=
  sorry

/-- If `p` satisfies Schlessinger's condition (S2), then so does
`residueChangeOver p`. -/
instance instHasSchlessingerS2 [IsFibered.InGroupoids p.op] [HasSchlessingerS2 p] :
    HasSchlessingerS2 (residueChangeOver Λ k l p) :=
  sorry

/-- If `p` satisfies the Rim-Schlessinger condition (RS), then so does
`residueChangeOver p`. -/
instance instHasRimSchlessinger [HasRimSchlessinger p] :
    HasRimSchlessinger (residueChangeOver Λ k l p) :=
  sorry

end residueChangeOver

end ArtinianLocalAlgCat
