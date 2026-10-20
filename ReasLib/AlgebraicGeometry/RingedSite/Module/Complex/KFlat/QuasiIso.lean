module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.QuasiIso
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Complex.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KFlatResolution
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor invariance for K-flat complexes on a ringed site

This leaf specializes the fixed-right K-flat tensor theorem to the canonical complex category of
module sheaves on a commutative ringed site.  The monoidal and homological infrastructure is
inferred from the shared `Complex.Monoidal` owner rather than rebuilt in the chapter.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.CochainComplex.IsKFlat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [UnivLE.{max u v, max u v}]

/-- Lemma 21.17.3 (06YP): tensoring a quasi-isomorphism on the left with a fixed K-flat complex
of module sheaves preserves quasi-isomorphisms. -/
@[stacks 06YP "fixed-right K-flat tensor invariance"]
theorem tensorHom_right_quasiIso
    (K : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)
    (hK : K.IsKFlat) {L M : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ}
    (f : L ⟶ M) [QuasiIso f] :
    QuasiIso (HomologicalComplex.tensorHom f (𝟙 K)) := sorry

/-- Lemma 21.17.12 (06YT): tensoring an arbitrary complex with a quasi-isomorphism between
K-flat complexes preserves quasi-isomorphisms. -/
@[stacks 06YT "K-flat tensor invariance in the varying factor"]
theorem quasiIso_tensorHom_right
    (F : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)
    {P Q : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ}
    (hP : P.IsKFlat) (hQ : Q.IsKFlat) (f : P ⟶ Q) [QuasiIso f] :
    QuasiIso (HomologicalComplex.tensorHom (𝟙 F) f) := sorry

end SheafOfModules.RingedSite.CochainComplex.IsKFlat

end
