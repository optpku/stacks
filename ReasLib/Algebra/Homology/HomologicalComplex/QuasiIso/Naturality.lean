module

public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Naturality of the homology isomorphism of a quasi-isomorphism

This file records the two orientations of naturality for `isoOfQuasiIsoAt`. The results apply
to an arbitrary complex shape and require a quasi-isomorphism only in the degree under study.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u w

namespace HomologicalComplex.isoOfQuasiIsoAt

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]
variable {ι : Type w} {c : ComplexShape ι}
variable {K L K' L' : HomologicalComplex C c} {i : ι}
variable [K.HasHomology i] [L.HasHomology i] [K'.HasHomology i] [L'.HasHomology i]

/-- The forward homology isomorphisms induced by two degreewise quasi-isomorphisms intertwine
the homology maps of a commuting square. -/
@[reassoc]
theorem hom_naturality (α : K ⟶ L) (α' : K' ⟶ L')
    (gK : K ⟶ K') (gL : L ⟶ L') [QuasiIsoAt α i] [QuasiIsoAt α' i]
    (comm : gK ≫ α' = α ≫ gL) :
    homologyMap gK i ≫ (isoOfQuasiIsoAt α' i).hom =
      (isoOfQuasiIsoAt α i).hom ≫ homologyMap gL i := sorry

/-- The inverse homology isomorphisms induced by two degreewise quasi-isomorphisms intertwine
the homology maps of a commuting square. -/
@[reassoc]
theorem inv_naturality (α : K ⟶ L) (α' : K' ⟶ L')
    (gK : K ⟶ K') (gL : L ⟶ L') [QuasiIsoAt α i] [QuasiIsoAt α' i]
    (comm : gK ≫ α' = α ≫ gL) :
    homologyMap gL i ≫ (isoOfQuasiIsoAt α' i).inv =
      (isoOfQuasiIsoAt α i).inv ≫ homologyMap gK i := sorry

end HomologicalComplex.isoOfQuasiIsoAt

end
