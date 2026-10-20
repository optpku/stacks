module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Slicing.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

open Scheme.Hom

/-- A Cohen--Macaulay, locally finitely presented groupoid scheme whose stabilizer is
locally of finite type and locally quasi-finite admits an affine immersed slice through
every finite-type point such that the slicing source and both restricted structure maps
are flat, locally finitely presented, and locally quasi-finite. -/
theorem existsAffineSliceFlatLocallyQuasiFinite
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [CohenMacaulay G.s.left] [LocallyOfFinitePresentation G.s.left]
    [CohenMacaulay G.t.left] [LocallyOfFinitePresentation G.t.left]
    [LocallyOfFiniteType (stabilizer G).X.hom.left]
    [LocallyQuasiFinite (stabilizer G).X.hom.left]
    (u : G.U.left) (h_u : IsFiniteTypePoint u) :
    ∃ U' : Over S, ∃ g : U' ⟶ G.U, ∃ u' : U'.left,
      IsAffine U'.left ∧ IsImmersion g.left ∧ g.left u' = u ∧
        LocallyOfFinitePresentation g.left ∧
        Flat (sliceSource G g).left ∧
        LocallyOfFinitePresentation (sliceSource G g).left ∧
        LocallyQuasiFinite (sliceSource G g).left ∧
        Flat (G.pullback g).s.left ∧
        LocallyOfFinitePresentation (G.pullback g).s.left ∧
        LocallyQuasiFinite (G.pullback g).s.left ∧
        Flat (G.pullback g).t.left ∧
        LocallyOfFinitePresentation (G.pullback g).t.left ∧
        LocallyQuasiFinite (G.pullback g).t.left := sorry

end AlgebraicGeometry.GroupoidScheme
