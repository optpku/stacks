/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeEmbedding
public import ReasLib.AlgebraicGeometry.Scheme.Etale.CartesianSystem

/-!
# Colimits of schemes in algebraic spaces

Under étale descent and a jointly surjective scheme presentation, a scheme colimit satisfying the
étale base-change criterion is also a colimit after embedding schemes into algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- A scheme colimit satisfying the étale base-change and descent criteria is also a colimit in
algebraic spaces after applying `schemeFunctor`. -/
theorem isColimit_ofOver {J : Type v} [Category.{v} J] [Small.{u} J] {S : Scheme.{u}}
    (D : J ⥤ Over S) (c : Cocone D)
    (hc : IsColimit ((Over.forget S).mapCocone c))
    (h_surj : AlgebraicGeometry.Surjective (Scheme.coproductToColimit c))
    (h_etale_colim : ∀ {U : Scheme.{u}} (f : U ⟶ c.pt.left) [AlgebraicGeometry.Etale f],
      IsColimit (Scheme.etalePullbackCocone c f))
    (h_ess : ∀ U : Scheme.CartesianEtaleSystem D,
      (∀ i, AlgebraicGeometry.IsSeparated (U.π.app i)) →
        Scheme.IsInEtaleEssImage c U) :
    Nonempty (IsColimit ((schemeFunctor S).mapCocone c)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
