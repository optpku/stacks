module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# Graph divisors over an arbitrary base

The graph of a morphism of `S`-schemes and its kernel ideal require no
separatedness, smoothness, properness, field base, or representability. The
Cartier and line-bundle specializations live in `Graph.Cartier`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section
universe u

namespace AlgebraicGeometry.SchemeOver

variable {S : Scheme.{u}} {X T : Over S}

/-- The graph of an `S`-morphism in `X ×ₛ T`. -/
def graph (x : T ⟶ X) : T.left ⟶ pullback X.hom T.hom :=
  pullback.lift x.left (𝟙 T.left) (x.w.trans (Category.id_comp _).symm)

@[reassoc (attr := simp)]
theorem graph_fst (x : T ⟶ X) : graph x ≫ pullback.fst X.hom T.hom = x.left := by
  exact CategoryTheory.Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem graph_snd (x : T ⟶ X) : graph x ≫ pullback.snd X.hom T.hom = 𝟙 T.left := by
  exact CategoryTheory.Limits.pullback.lift_snd _ _ _

/-- The kernel ideal of the graph; separatedness is not needed to form it. -/
def graphIdeal (x : T ⟶ X) : (pullback X.hom T.hom).IdealSheafData :=
  (graph x).ker

end AlgebraicGeometry.SchemeOver
