module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme

/-!
# Hyperplanes in projective space

A hyperplane in a chosen projective-space model is the zero scheme of a nonzero section of its
tautological sheaf. Such a hyperplane is itself a projective space of one lower dimension, and
the identification preserves the tautological sheaf.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpaceOver

variable {S : Scheme.{u}} {n : ℕ} (P : ProjectiveSpaceOver S n)

/-- The zero scheme of a section of the tautological sheaf on a chosen projective space. -/
noncomputable def tautologicalZeroScheme (s : P.tautologicalSheaf.sections) : Scheme :=
  @Scheme.zeroScheme P.scheme _ P.tautologicalSheaf
    (Scheme.Modules.Invertible.tensorRight_isEquivalence
      P.tautologicalSheaf_isInvertible) s

/-- The canonical immersion of the zero scheme of a tautological section into the chosen
projective space. -/
noncomputable def tautologicalZeroSchemeι (s : P.tautologicalSheaf.sections) :
    P.tautologicalZeroScheme s ⟶ P.scheme :=
  @Scheme.zeroSchemeι P.scheme _ P.tautologicalSheaf
    (Scheme.Modules.Invertible.tensorRight_isEquivalence
      P.tautologicalSheaf_isInvertible) s

end ProjectiveSpaceOver

section

variable {k : Type u} [Field k] {n : ℕ}

/-- A hyperplane in a chosen projective space over a field is a closed immersion cut out by a
nonzero section of the tautological sheaf. -/
class ProjectiveSpaceHyperplane
    (P : ProjectiveSpaceOver (Spec (CommRingCat.of k)) n)
    {H : Scheme.{u}} (i : H ⟶ P.scheme) : Prop extends IsClosedImmersion i where
  /-- The hyperplane is isomorphic over the ambient projective space to the zero scheme of a
  nonzero tautological section. -/
  exists_zeroScheme_presentation :
    ∃ s : P.tautologicalSheaf.sections,
      P.tautologicalSheaf.unitHomEquiv.symm s ≠ 0 ∧
        ∃ e : H ≅ P.tautologicalZeroScheme s,
          i = e.hom ≫ P.tautologicalZeroSchemeι s

namespace ProjectiveSpaceHyperplane

variable {P : ProjectiveSpaceOver (Spec (CommRingCat.of k)) n}
variable {H : Scheme.{u}} {i : H ⟶ P.scheme}

/-- A projective-space hyperplane is canonically a closed immersion into the ambient projective
space. -/
instance instIsClosedImmersion [h : ProjectiveSpaceHyperplane P i] :
    IsClosedImmersion i :=
  h.toIsClosedImmersion

/-- A morphism is a hyperplane inclusion exactly when it is a closed immersion identified with
the zero scheme of a nonzero tautological section. -/
theorem iff :
    ProjectiveSpaceHyperplane P i ↔
      IsClosedImmersion i ∧
        ∃ s : P.tautologicalSheaf.sections,
          P.tautologicalSheaf.unitHomEquiv.symm s ≠ 0 ∧
            ∃ e : H ≅ P.tautologicalZeroScheme s,
              i = e.hom ≫ P.tautologicalZeroSchemeι s := sorry

end ProjectiveSpaceHyperplane

/-- A hyperplane in positive-dimensional projective space over a field is a projective space of
one lower dimension over the base, and this identification preserves the tautological sheaf. -/
theorem exists_iso_projectiveSpace_pred_pullback_tautologicalSheaf_of_hyperplane
    (P : ProjectiveSpaceOver (Spec (CommRingCat.of k)) n) (hn : 1 ≤ n)
    {H : Scheme.{u}} (i : H ⟶ P.scheme) (hHyperplane : ProjectiveSpaceHyperplane P i) :
    ∃ (P' : ProjectiveSpaceOver (Spec (CommRingCat.of k)) (n - 1)) (φ : P'.scheme ≅ H)
      (e :
        (Scheme.Modules.pullback φ.hom).obj
            ((Scheme.Modules.pullback i).obj P.tautologicalSheaf) ≅
          P'.tautologicalSheaf),
      φ.hom ≫ i ≫ P.hom = P'.hom := sorry

end

end AlgebraicGeometry
