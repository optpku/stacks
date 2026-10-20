module

public import ReasLib.AlgebraicGeometry.SimplicialScheme.QCoh.Pullback
public import ReasLib.AlgebraicGeometry.SimplicialScheme.QCoh.Pushforward
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction

/-!
# Adjunction for quasi-coherent modules on simplicial schemes

The pullback-pushforward adjunction for quasi-coherent modules along a
cartesian morphism of simplicial schemes with flat cofaces and quasi-compact
quasi-separated components.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty Opposite
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.SimplicialObject

/-- Pullback of quasi-coherent modules is left adjoint to pushforward along a
cartesian morphism of simplicial schemes whose target face maps are flat and
whose components are quasi-compact and quasi-separated. -/
noncomputable def QCoh.pullbackPushforwardAdjunction
    {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U)
    [CategoryTheory.SimplicialObject.IsCartesian f]
    [∀ (n : ℕ) (j : Fin (n + 2)), Flat (U.δ j)]
    [∀ (n : ℕ), QuasiCompact (f.app (op ⦋n⦌))]
    [∀ (n : ℕ), QuasiSeparated (f.app (op ⦋n⦌))] :
    (QCoh.pullback f : QCoh U ⥤ QCoh V) ⊣
      (QCoh.pushforward f : QCoh V ⥤ QCoh U) :=
  ObjectProperty.FullSubcategory.adjunction (modulePullback f)
    (SheafOfModules.pushforward.{u} (structureSheafMap f))
    (SheafOfModules.pullbackPushforwardAdjunction (structureSheafMap f))
    (modulePullback_le_inverseImage f) (QCoh.pushforward.mapsTo f)

end AlgebraicGeometry.SimplicialObject
