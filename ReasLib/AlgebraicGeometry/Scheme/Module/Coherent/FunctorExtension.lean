module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.ProRealization
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Scheme

/-- A functor between coherent modules on Noetherian schemes extends to quasicoherent modules,
preserves filtered colimits, and is unique up to the unique natural isomorphism compatible with
its restriction to coherent modules. -/
theorem coherentFunctor_existsUniqueFilteredColimitExtension
    {X : Scheme.{u}} {Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace) :
    ∃ (G : Scheme.QCoh X ⥤ Scheme.QCoh Y)
      (eG : Scheme.coherentToQCoh X ⋙ G ≅ F ⋙ Scheme.coherentToQCoh Y)
      (_ : PreservesFilteredColimits G),
      ∀ (H : Scheme.QCoh X ⥤ Scheme.QCoh Y)
        (eH : Scheme.coherentToQCoh X ⋙ H ≅ F ⋙ Scheme.coherentToQCoh Y),
        PreservesFilteredColimits H →
          ∃! α : G ≅ H,
            Functor.isoWhiskerLeft (Scheme.coherentToQCoh X) α ≪≫ eH = eG := sorry

/-- The filtered-colimit-preserving extension of an additive functor between coherent modules
on Noetherian schemes preserves arbitrary coproducts. -/
theorem coherentFunctorExtension_preservesCoproducts
    {X : Scheme.{u}} {Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace)
    (G : Scheme.QCoh X ⥤ Scheme.QCoh Y) [PreservesFilteredColimits G]
    (eG : Scheme.coherentToQCoh X ⋙ G ≅ F ⋙ Scheme.coherentToQCoh Y)
    [F.Additive] (J : Type w) :
    PreservesColimitsOfShape (Discrete J) G := sorry

/-- The filtered-colimit-preserving extension of an exact functor between coherent modules
on Noetherian schemes is exact. -/
theorem coherentFunctorExtension_exact
    {X : Scheme.{u}} {Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace)
    (G : Scheme.QCoh X ⥤ Scheme.QCoh Y) [PreservesFilteredColimits G]
    (eG : Scheme.coherentToQCoh X ⋙ G ≅ F ⋙ Scheme.coherentToQCoh Y)
    (hF : exactFunctor (RingedSpace.Coh X.toRingedSpace)
      (RingedSpace.Coh Y.toRingedSpace) F) :
    exactFunctor (Scheme.QCoh X) (Scheme.QCoh Y) G := sorry

/-- The filtered-colimit-preserving extension of a left exact functor between coherent modules
on Noetherian schemes is left exact. -/
theorem coherentFunctorExtension_leftExact
    {X : Scheme.{u}} {Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace)
    (G : Scheme.QCoh X ⥤ Scheme.QCoh Y) [PreservesFilteredColimits G]
    (eG : Scheme.coherentToQCoh X ⋙ G ≅ F ⋙ Scheme.coherentToQCoh Y)
    (hF : leftExactFunctor (RingedSpace.Coh X.toRingedSpace)
      (RingedSpace.Coh Y.toRingedSpace) F) :
    leftExactFunctor (Scheme.QCoh X) (Scheme.QCoh Y) G := sorry

/-- The filtered-colimit-preserving extension of a right exact functor between coherent modules
on Noetherian schemes is right exact. -/
theorem coherentFunctorExtension_rightExact
    {X : Scheme.{u}} {Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace)
    (G : Scheme.QCoh X ⥤ Scheme.QCoh Y) [PreservesFilteredColimits G]
    (eG : Scheme.coherentToQCoh X ⋙ G ≅ F ⋙ Scheme.coherentToQCoh Y)
    (hF : rightExactFunctor (RingedSpace.Coh X.toRingedSpace)
      (RingedSpace.Coh Y.toRingedSpace) F) :
    rightExactFunctor (Scheme.QCoh X) (Scheme.QCoh Y) G := sorry

end AlgebraicGeometry.Scheme
