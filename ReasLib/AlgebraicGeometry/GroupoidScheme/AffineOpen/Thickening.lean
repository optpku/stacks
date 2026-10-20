module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.GroupoidScheme.AffineOpen
public import ReasLib.AlgebraicGeometry.GroupoidScheme.FinitePresentation

/-!
# Invariant affine thickenings of groupoid schemes
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- A finite groupoid scheme with finitely presented source and target maps and a
quasi-separated object scheme admits, through any finite family of points whose orbits
consist of generic points of irreducible components, an invariant affine closed thickening
of finite presentation inside an invariant affine open. The restricted source and target
maps are finite locally free. -/
theorem exists_invariantAffineOpenThickening_of_finitePresentation {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.s.left] [IsFinite G.t.left]
    [Scheme.Hom.FinitePresentation G.s.left]
    [Scheme.Hom.FinitePresentation G.t.left] [QuasiSeparatedSpace G.U.left]
    {m : ℕ} (u : Fin m → G.U.left)
    (h_orbit : ∀ j, G.t.left '' (G.s.left ⁻¹' {u j}) ⊆ genericPoints G.U.left) :
    ∃ (V : Scheme.affineOpens G.U.left) (Z : Scheme.IdealSheafData (V : Scheme)),
      let i : Over.mk ((Z.subschemeι ≫ (V : Scheme.Opens G.U.left).ι) ≫ G.U.hom) ⟶ G.U :=
        Over.homMk (Z.subschemeι ≫ (V : Scheme.Opens G.U.left).ι)
      ∃ (h_V_invariant :
          G.toPreRelation.IsOpenInvariant (V : Scheme.Opens G.U.left))
        (h_Z_invariant :
          G.toPreRelation.IsInvariant
            (Subobject.mk (Z.subschemeι ≫ (V : Scheme.Opens G.U.left).ι)))
        (h_points :
          ∀ j, u j ∈ Set.range (Z.subschemeι ≫ (V : Scheme.Opens G.U.left).ι))
        (h_Z_affine : IsAffine Z.subscheme)
        (h_thickening : IsThickening Z.subschemeι)
        (h_finitePresentation : Scheme.Hom.FinitePresentation Z.subschemeι)
        (h_source : IsFiniteLocallyFree (G.pullback i).s.left),
        IsFiniteLocallyFree (G.pullback i).t.left := sorry

/-- Given finitely many points of a locally Noetherian groupoid scheme whose orbits consist
of generic points of irreducible components, there is an invariant affine closed thickening
through those points inside an invariant affine open, with finite locally free restricted
source and target maps. -/
theorem exists_invariantAffineOpenThickening {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.s.left] [IsFinite G.t.left] [IsLocallyNoetherian G.U.left]
    {m : ℕ} (u : Fin m → G.U.left)
    (h_orbit : ∀ j, G.t.left '' (G.s.left ⁻¹' {u j}) ⊆ genericPoints G.U.left) :
    ∃ (V : Scheme.affineOpens G.U.left) (Z : Scheme.IdealSheafData (V : Scheme)),
      let i : Over.mk ((Z.subschemeι ≫ (V : Scheme.Opens G.U.left).ι) ≫ G.U.hom) ⟶ G.U :=
        Over.homMk (Z.subschemeι ≫ (V : Scheme.Opens G.U.left).ι)
      ∃ (h_V_invariant :
          G.toPreRelation.IsOpenInvariant (V : Scheme.Opens G.U.left))
        (h_Z_invariant :
          G.toPreRelation.IsInvariant
            (Subobject.mk (Z.subschemeι ≫ (V : Scheme.Opens G.U.left).ι)))
        (h_points :
          ∀ j, u j ∈ Set.range (Z.subschemeι ≫ (V : Scheme.Opens G.U.left).ι))
        (h_Z_affine : IsAffine Z.subscheme)
        (h_thickening : IsThickening Z.subschemeι)
        (h_source : IsFiniteLocallyFree (G.pullback i).s.left),
        IsFiniteLocallyFree (G.pullback i).t.left := sorry

end AlgebraicGeometry.GroupoidScheme
