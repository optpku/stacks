module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Lifting quasi-isomorphisms along surjections of ring sheaves

Quasi-isomorphisms into a scalar extension admit quasi-isomorphic replacements
over the original ring sheaf whose scalar extensions factor up to homotopy.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace SheafOfModules.RingedSite

/-- Along a locally surjective morphism of commutative ring sheaves, a
quasi-isomorphism into the scalar extension of a complex admits a
quasi-isomorphic replacement over the original ring sheaf whose scalar
extension factors through the given quasi-isomorphism up to homotopy. -/
@[stacks 0DIX]
theorem exists_quasiIso_homotopyFactor
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [HasSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {O O₀ : Sheaf J CommRingCat.{w}} (π : O ⟶ O₀)
    [Sheaf.IsLocallySurjective π]
    (F : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ)
    (K₀ : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O₀) ℤ)
    (α : K₀ ⟶ (extendComplex π).obj F) [QuasiIso α] :
    ∃ (G : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ) (q : G ⟶ F),
      QuasiIso q ∧ ∃ (h : (extendComplex π).obj G ⟶ K₀),
        Nonempty (Homotopy ((extendComplex π).map q) (h ≫ α)) := sorry

end SheafOfModules.RingedSite
