module

public import stacks_project.Chap79.Remark_79_12_6_Comparison

/-!
# Compactly supported étale 𝐅₂ versus the finite part

A separated locally quasi-finite morphism of schemes has
`f_! 𝐅₂ ≅ (X/Y)_fin` on the small étale site, identifying compactly
supported 𝐅₂-sections with finite-part pairs `(V ⟶ Y, Supp(s))`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale Opposite
open AlgebraicGeometry.AlgebraicSpace.FinitePart

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]

/-- Remark 79.12.6 (1): if `V ⟶ Y` is étale and `s` is a section of
`f_! 𝐅₂` over `V`, then `s` is an 𝐅₂-section on `V ×_Y X` with proper
support `Z = Supp(s)` over `V`. Local quasi-finiteness upgrades
`Z ⟶ V` to a finite morphism, and the support of a constant abelian
sheaf is open, so the pair `(V ⟶ Y, Supp(s))` satisfies 79.12.0.1. -/
@[stacks 04PJ]
theorem ofSection_spec [AlgebraicGeometry.IsSeparated f]
    [LocallyQuasiFinite f] [LocallyOfFiniteType f] (V : Y.Etale)
    (σ : compactSupportSections f (constantF2 X) V) :
    HasProperSupport f (constantF2 X) V
        ((compactSupportSections f (constantF2 X) V).subtype σ) ∧
      (ofSection f V σ).a = etaleOverMap V ∧
      (ofSection f V σ).Z.carrier =
        fiberComparisonPointsHomeomorph f V ''
          (abelianSheafSectionSupport (constantF2 X)
            ((smallEtalePullback f).obj V)
            ((compactSupportSections f (constantF2 X) V).subtype σ)).carrier ∧
      IsOpen (ofSection f V σ).Z.carrier ∧
      IsFinite (ofSection f V σ).pr0 :=
  sorry

/-- Remark 79.12.6 (2): for a separated locally quasi-finite morphism of
schemes, `f_! 𝐅₂ ≅ (X/Y)_fin` after restriction to `Y_étale`. -/
@[stacks 04PJ]
abbrev finitePartEtaleIso [AlgebraicGeometry.IsSeparated f]
    [LocallyQuasiFinite f] [LocallyOfFiniteType f] :=
  lowerShriekF2Iso f

/-- Components of `finitePartEtaleIso` send compactly supported 𝐅₂-sections to
the corresponding finite-part pairs. -/
theorem finitePartEtaleIso_hom_app [AlgebraicGeometry.IsSeparated f]
    [LocallyQuasiFinite f] [LocallyOfFiniteType f] (V : Y.Etale)
    (σ :
      (CategoryTheory.forget AddCommGrpCat.{u}).obj
        (((etaleLowerShriek f).obj (constantF2 X)).obj.obj (op V))) :
    (finitePartEtaleIso f).hom.app (op V) σ =
      equivShrink _ (ofSection f V σ) :=
  sorry

/-- Remark 79.12.6 (3): the comparison identifies 𝐅₂-addition of compactly
supported sections with symmetric difference of finite-part opens, and
identifies 𝐅₂-multiplication with intersection, recovering the 𝐅₂-algebra
structure of Remark 79.12.5. -/
@[stacks 04PJ]
theorem ofSection_add_mul [AlgebraicGeometry.IsSeparated f]
    [LocallyQuasiFinite f] [LocallyOfFiniteType f]
    (V : Y.Etale) (σ τ : compactSupportSections f (constantF2 X) V) :
    ofSection f V (σ + τ) = (ofSection f V σ).add (ofSection f V τ) rfl ∧
      ofSection f V (sectionMul f V σ τ) =
        (ofSection f V σ).mul (ofSection f V τ) rfl :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePart
