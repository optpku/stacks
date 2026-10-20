module

public import stacks_project.Chap79.Remark_79_12_6_Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.CompactSupport
import StacksCheckRecall

/-! # Compactly supported étale two-element sections and the finite-part sheaf -/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale Opposite
open AlgebraicGeometry.AlgebraicSpace.FinitePart
universe u

/- Remark 79.12.6 (1): if `V ⟶ Y` is étale and `s` is a section of
`f_! 𝐅₂` over `V`, then `s` is an 𝐅₂-section on `V ×_Y X` with proper
support `Z = Supp(s)` over `V`. Local quasi-finiteness upgrades
`Z ⟶ V` to a finite morphism, and the support of a constant abelian
sheaf is open, so the pair `(V ⟶ Y, Supp(s))` satisfies 79.12.0.1. -/
@[stacks 04PJ] #check (AlgebraicGeometry.AlgebraicSpace.FinitePart.ofSection_spec :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [AlgebraicGeometry.IsSeparated f] [LocallyQuasiFinite f] (V : Y.Etale)
    (σ : compactSupportSections f (constantF2 X) V),
    HasProperSupport f (constantF2 X) V
        ((compactSupportSections f (constantF2 X) V).subtype σ) ∧
      (ofSection f V σ).a = etaleOverMap V ∧
      (ofSection f V σ).Z.carrier =
        fiberComparisonPointsHomeomorph f V ''
          (abelianSheafSectionSupport (constantF2 X)
            ((smallEtalePullback f).obj V)
            ((compactSupportSections f (constantF2 X) V).subtype σ)).carrier ∧
      IsOpen (ofSection f V σ).Z.carrier ∧
      IsFinite (ofSection f V σ).pr0)

/- Remark 79.12.6 (2): for a separated locally quasi-finite morphism of
schemes, `f_! 𝐅₂ ≅ (X/Y)_fin` after restriction to `Y_étale`. -/
@[stacks 04PJ] #check (AlgebraicGeometry.AlgebraicSpace.FinitePart.finitePartEtaleIso :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [AlgebraicGeometry.IsSeparated f] [LocallyQuasiFinite f],
    ((etaleLowerShriek f).obj (constantF2 X)).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u} ≅ (finitePartEtale f).obj)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.finitePartEtaleIso_hom_app :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [AlgebraicGeometry.IsSeparated f] [LocallyQuasiFinite f] (V : Y.Etale)
    (σ :
      (CategoryTheory.forget AddCommGrpCat.{u}).obj
        (((etaleLowerShriek f).obj (constantF2 X)).obj.obj (op V))),
    (finitePartEtaleIso f).hom.app (op V) σ =
      (finitePart_obj_equiv (ofSchemeHom f) ((Scheme.Etale.forget Y).obj V)).symm (ofSection f V σ))

/- Remark 79.12.6 (3): the comparison identifies 𝐅₂-addition of compactly
supported sections with symmetric difference of finite-part opens, and
identifies 𝐅₂-multiplication with intersection, recovering the 𝐅₂-algebra
structure of Remark 79.12.5. -/
@[stacks 04PJ] #check (AlgebraicGeometry.AlgebraicSpace.FinitePart.ofSection_add_mul :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [AlgebraicGeometry.IsSeparated f] [LocallyQuasiFinite f] (V : Y.Etale) (σ τ : compactSupportSections f (constantF2 X) V),
    ofSection f V (σ + τ) = (ofSection f V σ).add (ofSection f V τ) rfl ∧
      ofSection f V (sectionMul f V σ τ) =
        (ofSection f V σ).mul (ofSection f V τ) rfl)
