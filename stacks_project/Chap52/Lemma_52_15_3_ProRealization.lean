module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.ProRealization

/-!
# Pro-realization compatibility checks

The pro-realization API is publicly imported from its mathematical owner.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

#check (coherentToQCoh : ∀ (X : Scheme.{u}) [IsNoetherian X],
  RingedSpace.Coh X.toRingedSpace ⥤ QCoh X)

#check (coherentToQCoh_obj : ∀ (X : Scheme.{u}) [IsNoetherian X]
  (F : RingedSpace.Coh X.toRingedSpace), ((coherentToQCoh X).obj F).obj = F.obj)

#check (coherentToQCoh_map : ∀ (X : Scheme.{u}) [IsNoetherian X]
  {F G : RingedSpace.Coh X.toRingedSpace} (f : F ⟶ G),
  ((coherentToQCoh X).map f).hom = f.hom)

namespace CoherentFormalModules

#check (proFunctor : ∀ {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData),
  CoherentFormalModules X I ⥤ Pro (QCoh X))

#check (proFunctor_obj : ∀ {X : Scheme.{u}} [IsNoetherian X]
  (I : X.IdealSheafData) (F : CoherentFormalModules X I),
  (proFunctor I).obj F =
    (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).obj (F.obj ⋙ coherentToQCoh X))

#check (proFunctor_map : ∀ {X : Scheme.{u}} [IsNoetherian X]
  (I : X.IdealSheafData) {F G : CoherentFormalModules X I} (f : F ⟶ G),
  (proFunctor I).map f =
    (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).map (Functor.whiskerRight f.hom (coherentToQCoh X)))

#check (proFunctor_map_bijective : ∀ {X : Scheme.{u}} [IsNoetherian X]
  (I : X.IdealSheafData) (F G : CoherentFormalModules X I),
  Function.Bijective (fun f : F ⟶ G ↦ (proFunctor I).map f))

#check (proFunctorFull : ∀ {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData),
  (proFunctor I).Full)

#check (proFunctorFaithful : ∀ {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData),
  (proFunctor I).Faithful)

end CoherentFormalModules

end AlgebraicGeometry.Scheme
