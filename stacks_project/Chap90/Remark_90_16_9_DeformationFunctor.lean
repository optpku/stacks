/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Elements
public import stacks_project.Chap90.Definition_90_16_8_RimSchlessinger
public import stacks_project.Chap90.Remark_90_6_3_PredeformationFunctor

/-!
# Deformation functors

A functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v` is a deformation functor when it is
a predeformation functor and the associated cofibered set satisfies (RS).
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- A functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v` is a deformation functor if it is
a predeformation functor and the associated cofibered set `CategoryOfElements.π F`
satisfies the Rim-Schlessinger condition (RS). -/
class IsDeformationFunctor (F : ArtinianLocalAlgCat Λ k ⥤ Type v) : Prop
    extends IsPredeformationFunctor F where
  /-- The associated cofibered set satisfies (RS). -/
  [hasRimSchlessinger : HasRimSchlessinger (CategoryOfElements.π F)]

/-- A predeformation functor whose associated cofibered set satisfies (RS) is a
deformation functor. -/
instance instIsDeformationFunctor {F : ArtinianLocalAlgCat Λ k ⥤ Type v}
    [IsPredeformationFunctor F] [HasRimSchlessinger (CategoryOfElements.π F)] :
    IsDeformationFunctor F where

/-- A functor is a deformation functor iff it is a predeformation functor and the
associated cofibered set satisfies (RS). -/
theorem isDeformationFunctor_iff (F : ArtinianLocalAlgCat Λ k ⥤ Type v) :
    IsDeformationFunctor F ↔
      IsPredeformationFunctor F ∧ HasRimSchlessinger (CategoryOfElements.π F) :=
  sorry

end CategoryTheory.Functor
