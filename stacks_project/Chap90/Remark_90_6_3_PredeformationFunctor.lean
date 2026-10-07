module

public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Logic.Unique
public import stacks_project.Chap90.Definition_90_16_8_Predeformation

/-!
# Predeformation functors

A functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v` is a predeformation functor when
its value at `ArtinianLocalAlgCat.residue Λ k` is a singleton.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- A functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v` is a predeformation functor if
`F.obj (ArtinianLocalAlgCat.residue Λ k)` is a singleton. -/
class IsPredeformationFunctor (F : ArtinianLocalAlgCat Λ k ⥤ Type v) : Prop where
  /-- The value at the residue field is a singleton. -/
  unique_residue : Nonempty (Unique (F.obj (ArtinianLocalAlgCat.residue Λ k)))

/-- A functor to types with a unique value at the residue field is a predeformation functor. -/
instance instIsPredeformationFunctor
    {F : ArtinianLocalAlgCat Λ k ⥤ Type v}
    [Unique (F.obj (ArtinianLocalAlgCat.residue Λ k))] :
    IsPredeformationFunctor F :=
  ⟨⟨inferInstance⟩⟩

/-- A functor is a predeformation functor iff its value at the residue field is a singleton. -/
theorem isPredeformationFunctor_iff (F : ArtinianLocalAlgCat Λ k ⥤ Type v) :
    IsPredeformationFunctor F ↔
      Nonempty (Unique (F.obj (ArtinianLocalAlgCat.residue Λ k))) := sorry

end CategoryTheory.Functor
