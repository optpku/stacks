/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.SetTheory.Cardinal.ENat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.EtaleLocal

@[expose] public section

open CategoryTheory
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Germ.Hom.Representative

/-- The transcendence degree of the residue-field extension induced by a representative of a
morphism of scheme germs, with all infinite cardinal values identified with `⊤ : ℕ∞`. -/
noncomputable def residueFieldTrdeg {X Y : Germ} (f : Representative X Y) : ℕ∞ :=
  Cardinal.toENat
    (Algebra.trdeg
      (Y.scheme.residueField (f.hom (X.pointIn f.neighborhood f.mem_neighborhood)))
      (f.neighborhood.toScheme.residueField
        (X.pointIn f.neighborhood f.mem_neighborhood)))

/-- The representative residue-field transcendence degree is the extended-natural projection
of the cardinal-valued transcendence degree at the distinguished source point. -/
theorem residueFieldTrdeg_def {X Y : Germ} (f : Representative X Y) :
    residueFieldTrdeg f =
      Cardinal.toENat
        (Algebra.trdeg
          (Y.scheme.residueField (f.hom (X.pointIn f.neighborhood f.mem_neighborhood)))
          (f.neighborhood.toScheme.residueField
            (X.pointIn f.neighborhood f.mem_neighborhood))) := sorry

/-- Equivalent neighborhood representatives induce the same residue-field transcendence
degree. -/
theorem residueFieldTrdeg_eq_of_equivalent {X Y : Germ} {f g : Representative X Y}
    (h : Equivalent f g) : residueFieldTrdeg f = residueFieldTrdeg g := sorry

end AlgebraicGeometry.Scheme.Germ.Hom.Representative

namespace AlgebraicGeometry.Scheme.Germ.Hom

/-- The residue-field transcendence degree of a morphism of scheme germs, valued in `ℕ∞`. -/
noncomputable def residueFieldTrdeg {X Y : Germ} (f : Hom X Y) : ℕ∞ :=
  lift Representative.residueFieldTrdeg
    (fun _ _ h ↦ Representative.residueFieldTrdeg_eq_of_equivalent h) f

/-- The residue-field transcendence degree of a represented germ morphism is computed on its
representative. -/
theorem residueFieldTrdeg_mk {X Y : Germ} (f : Representative X Y) :
    residueFieldTrdeg (mk f) = f.residueFieldTrdeg := sorry

end AlgebraicGeometry.Scheme.Germ.Hom

namespace AlgebraicGeometry.Scheme.Germ.MorphismProperty

/-- The property that a morphism of scheme germs has residue-field transcendence degree `r`. -/
def residueFieldTrdegEq (r : ℕ∞) : CategoryTheory.MorphismProperty Germ :=
  fun {_ _} f ↦ Hom.residueFieldTrdeg f = r

/-- A germ morphism satisfies `residueFieldTrdegEq r` exactly when its residue-field
transcendence degree is `r`. -/
theorem residueFieldTrdegEq_iff {X Y : Germ} (r : ℕ∞) (f : X ⟶ Y) :
    residueFieldTrdegEq r f ↔ Hom.residueFieldTrdeg f = r := sorry

/-- For every extended natural number `r`, residue-field transcendence degree equal to `r` is
étale local on the source-and-target for morphisms of scheme germs. -/
theorem residueFieldTrdegEq_isEtaleLocal (r : ℕ∞) :
    IsEtaleLocal (residueFieldTrdegEq r) := sorry

end AlgebraicGeometry.Scheme.Germ.MorphismProperty
