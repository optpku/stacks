module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver

/-- A morphism between finite-type separated schemes over a Noetherian base is locally of finite type. -/
instance instLocallyOfFiniteTypeHom
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) :
    LocallyOfFiniteType f.hom.left := sorry

/-- A morphism between finite-type separated schemes over a Noetherian base is separated. -/
instance instIsSeparatedHom
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) :
    IsSeparated f.hom.left := sorry

/-- A morphism between finite-type separated schemes over a Noetherian base is locally of finite presentation. -/
instance instLocallyOfFinitePresentationHom
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) :
    LocallyOfFinitePresentation f.hom.left := sorry

end AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver
