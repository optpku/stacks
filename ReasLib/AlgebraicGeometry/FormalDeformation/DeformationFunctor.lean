module

public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Functor
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.Associated
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger.Schlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.Types

/-!
# Deformation functors

A deformation functor is a predeformation functor whose category-of-elements
projection satisfies the Rim-Schlessinger condition.
-/

@[expose] public section

open CategoryTheory

universe u v w

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

/-- A deformation functor satisfies Schlessinger's condition (H2). -/
instance instHasSchlessingerH2_of_isDeformationFunctor
    {G : ArtinianLocalAlgCat Λ k ⥤ Type v} [IsDeformationFunctor G] :
    HasSchlessingerH2 G :=
  (hasSchlessingerS2_iff_hasSchlessingerH2 G).mp
    (@HasRimSchlessinger.toHasSchlessingerS2 _ _ _ _ _ _ _ _ _
      (CategoryOfElements.π G) (IsDeformationFunctor.hasRimSchlessinger (F := G)))

/-- A functor is a deformation functor iff it is a predeformation functor and the
associated cofibered set satisfies (RS). -/
theorem isDeformationFunctor_iff (F : ArtinianLocalAlgCat Λ k ⥤ Type v) :
    IsDeformationFunctor F ↔
      IsPredeformationFunctor F ∧ HasRimSchlessinger (CategoryOfElements.π F) :=
  sorry

/-- A functor to types is a deformation functor iff its category-of-elements
projection is a deformation category. -/
theorem isDeformationFunctor_iff_isDeformationCategory
    (F : ArtinianLocalAlgCat Λ k ⥤ Type v) :
    IsDeformationFunctor F ↔ IsDeformationCategory (CategoryOfElements.π F) :=
  sorry

/-- The functor of isomorphism classes associated to a deformation category is a
predeformation functor. -/
instance instIsPredeformationFunctor_isoClassFunctor
    {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsDeformationCategory p] :
    IsPredeformationFunctor (isoClassFunctor p) :=
  fiberIsoClassPresheaf_isPredeformationFunctor p

/-- The functor of isomorphism classes of a deformation category is a deformation
functor iff its category-of-elements projection satisfies (RS). -/
theorem isoClassFunctor_isDeformationFunctor_iff
    {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsDeformationCategory p] :
    IsDeformationFunctor (isoClassFunctor p) ↔
      HasRimSchlessinger (CategoryOfElements.π (isoClassFunctor p)) :=
  sorry

end CategoryTheory.Functor
