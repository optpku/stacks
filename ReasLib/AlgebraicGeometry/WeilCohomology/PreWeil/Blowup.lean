module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.GDelta.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil.AxiomA8
public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil.Pushforward

@[expose] public section

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace

universe u v w

namespace WeilCohomology.PreWeilTheory

/-- In a pre-Weil theory satisfying Axiom A8, pushforward along the blowup of a nonempty
equidimensional smooth projective scheme in a smooth nowhere dense center sends `1` to `1`. -/
theorem pushforward_one_of_isBlowupOfSmoothCenter
    {k : Type u} [Field k]
    {F : Type v} [Field F] [CharZero F]
    {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
    {H Picard Cycle : ULiftHom.{u + 1} (SchemeOverField k) → Type w}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    [∀ X, AddCommGroup (Picard X)] [∀ X, Ring (Cycle X)]
    (T : PreWeilTheory F TateLine
      (ULiftHom.{u + 1} (SchemeOverField k)) H Picard Cycle)
    (hA8 : T.SatisfiesAxiomA8)
    {X' X : SchemeOverField k} {d : ℕ}
    [Nonempty X.left] [EquidimensionalSpace X.left] [Smooth X.hom] [Projective X.hom]
    (h_dim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hX : T.IsNonemptyEquidimensional (ULiftHom.up.obj X) d)
    (hX' : T.IsNonemptyEquidimensional (ULiftHom.up.obj X') d) (b : X' ⟶ X)
    (I : X.left.IdealSheafData) [IsBlowup b.left I]
    [Smooth (I.subschemeι ≫ X.hom)]
    (h_center_nowhereDense : IsNowhereDense (I.support : Set X.left))
    (h_blowup : T.IsBlowupOfSmoothCenter (ULiftHom.up.map b)) :
    T.pushforward hX' hX (ULiftHom.up.map b) 1 = 1 := sorry

end WeilCohomology.PreWeilTheory
