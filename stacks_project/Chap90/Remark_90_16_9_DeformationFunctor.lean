module

public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationFunctor

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

open CategoryTheory.Functor

#check (CategoryTheory.Functor.IsDeformationFunctor :
  (ArtinianLocalAlgCat Λ k ⥤ Type v) → Prop)

variable {F : ArtinianLocalAlgCat Λ k ⥤ Type v}
  [IsPredeformationFunctor F] [HasRimSchlessinger (CategoryOfElements.π F)]

#check (CategoryTheory.Functor.instIsDeformationFunctor : IsDeformationFunctor F)

#check (CategoryTheory.Functor.isDeformationFunctor_iff :
  ∀ (G : ArtinianLocalAlgCat Λ k ⥤ Type v),
    IsDeformationFunctor G ↔
      IsPredeformationFunctor G ∧ HasRimSchlessinger (CategoryOfElements.π G))
