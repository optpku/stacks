/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Algebra.Map

/-!
# Affine formulas for maps of conormal algebras

The canonical map of conormal algebras associated to a commutative square is characterized
degreewise on compatible affine charts by the induced map of associated graded rings.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ConormalAlgebra

variable {Z X Z' X' : Scheme.{u}}
variable {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}

/-- The inverse image of a compatible ambient affine open contains the inverse image along the
upper horizontal morphism of the corresponding immersed affine open. -/
theorem affinePreimage_le (sq : CommSq f i i' g)
    (U : X.affineOpens) (U' : X'.affineOpens)
    (e : (U : X.Opens) ≤ g ⁻¹ᵁ (U' : X'.Opens)) :
    i ⁻¹ᵁ (U : X.Opens) ≤ f ⁻¹ᵁ (i' ⁻¹ᵁ (U' : X'.Opens)) := by
  intro z hz
  change (f ≫ i').base z ∈ (U' : X'.Opens)
  rw [sq.w]
  exact e hz

/-- The map on sections over compatible affine charts induced by a candidate homomorphism of
pulled-back conormal algebras. -/
noncomputable def mapOnAffineSections (sq : CommSq f i i' g)
    (tau : GradedAlgebraSheaf.Hom.{u, u}
      (Scheme.Modules.GradedAlgebra.pullback f (Scheme.ConormalAlgebra i'))
      (Scheme.ConormalAlgebra i))
    (n : ℕ) (U : X.affineOpens) (U' : X'.affineOpens)
    (e : (U : X.Opens) ≤ g ⁻¹ᵁ (U' : X'.Opens)) :
    ((Scheme.ConormalAlgebra i').obj n).val.obj
        (Opposite.op (i' ⁻¹ᵁ (U' : X'.Opens))) →+
      ((Scheme.ConormalAlgebra i).obj n).val.obj
        (Opposite.op (i ⁻¹ᵁ (U : X.Opens))) :=
  (((Scheme.ConormalAlgebra i).obj n).val.map
      (homOfLE (affinePreimage_le sq U U' e)).op).hom.toAddMonoidHom.comp
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (tau.hom n)).val.app
        (Opposite.op (i' ⁻¹ᵁ (U' : X'.Opens)))).hom.toAddMonoidHom

/-- Evaluation of the affine section map is the adjoint component followed by restriction to
the immersed inverse-image open. -/
@[simp] theorem mapOnAffineSections_apply (sq : CommSq f i i' g)
    (tau : GradedAlgebraSheaf.Hom.{u, u}
      (Scheme.Modules.GradedAlgebra.pullback f (Scheme.ConormalAlgebra i'))
      (Scheme.ConormalAlgebra i))
    (n : ℕ) (U : X.affineOpens) (U' : X'.affineOpens)
    (e : (U : X.Opens) ≤ g ⁻¹ᵁ (U' : X'.Opens))
    (x : ((Scheme.ConormalAlgebra i').obj n).val.obj
      (Opposite.op (i' ⁻¹ᵁ (U' : X'.Opens)))) :
    mapOnAffineSections sq tau n U U' e x =
      ((((Scheme.ConormalAlgebra i).obj n).val.map
        (homOfLE (affinePreimage_le sq U U' e)).op).hom)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
          (tau.hom n)).val.app
            (Opposite.op (i' ⁻¹ᵁ (U' : X'.Opens))) x) := rfl

/-- A homomorphism of pulled-back conormal algebras has the canonical affine formula when its
degreewise action on every compatible pair of affine closed charts is induced by the ambient
map on associated graded rings. -/
def IsAffineMap (sq : CommSq f i i' g)
    (tau : GradedAlgebraSheaf.Hom.{u, u}
      (Scheme.Modules.GradedAlgebra.pullback f (Scheme.ConormalAlgebra i'))
      (Scheme.ConormalAlgebra i)) : Prop :=
  ∀ (U : X.affineOpens) (U' : X'.affineOpens)
    (e : (U : X.Opens) ≤ g ⁻¹ᵁ (U' : X'.Opens))
    (hU : IsAffineChart i U) (hU' : IsAffineChart i' U'),
        ∀ (n : ℕ)
          (x : Ideal.AssociatedGraded.grade
            (immersionAffineConormalIdeal i' (U' : X'.Opens)) n),
          mapOnAffineSections sq tau n U U' e (affineGradeToSections i' U' n x) =
            affineGradeToSections i U n
              (Ideal.AssociatedGraded.mapGrade
                (immersionAffineConormalIdeal i' (U' : X'.Opens))
                (immersionAffineConormalIdeal i (U : X.Opens))
                ((g.appLE (U' : X'.Opens) (U : X.Opens) e).hom)
                (AlgebraicGeometry.immersionAffineConormalIdeal_le_comap sq U U' e) n x)

/-- For immersion sides, the affine associated-graded formula is equivalent to the internal
sheafification-and-adjunction specification. -/
theorem isAffineMap_iff_isMap [IsImmersion i] [IsImmersion i']
    (sq : CommSq f i i' g)
    (tau : GradedAlgebraSheaf.Hom.{u, u}
      (Scheme.Modules.GradedAlgebra.pullback f (Scheme.ConormalAlgebra i'))
      (Scheme.ConormalAlgebra i)) :
    IsAffineMap sq tau ↔ IsMap sq tau := sorry

/-- The canonical conormal-algebra comparison satisfies the affine associated-graded formula. -/
theorem map_affine [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    IsAffineMap sq (map sq) :=
  (isAffineMap_iff_isMap sq (map sq)).2 (map_isMap sq)

/-- There is a unique conormal-algebra comparison satisfying the affine associated-graded
formula on every compatible pair of affine closed charts. -/
theorem existsUnique_map [IsImmersion i] [IsImmersion i'] (sq : CommSq f i i' g) :
    ∃! tau : GradedAlgebraSheaf.Hom.{u, u}
      (Scheme.Modules.GradedAlgebra.pullback f (Scheme.ConormalAlgebra i'))
      (Scheme.ConormalAlgebra i), IsAffineMap sq tau :=
  ⟨map sq, map_affine sq, fun tau h_tau ↦
    eq_map sq ((isAffineMap_iff_isMap sq tau).1 h_tau)⟩

end AlgebraicGeometry.Scheme.ConormalAlgebra
