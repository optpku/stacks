module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.Chaotic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-coherent derived modules over a category with a terminal object

On a chaotic ringed site, a quasi-coherent derived module is
determined by its derived sections at a terminal object.  The canonical map on Hom sets is kept
as explicit data; equivalence and bijectivity are separate propositions.
-/

@[expose] public section

noncomputable section

-- Local instance justification (defeq pin): the site-presented and bundled module categories
-- use the same existing standard derived localization.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
  RingedSite.Hom.CommRingPresentation.moduleHasDerivedCategory

open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite

universe u v w

namespace CategoryTheory.ModulesOnCategory.Chaotic.Terminal

variable {C : Type u} [Category.{v} C]
variable (O : Sheaf (⊥ : GrothendieckTopology C)
  CommRingCat.{max (max u v) w})
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose
  (forget₂ CommRingCat.{max (max u v) w} RingCat.{max (max u v) w})]

/-- Derived sections at `X`, restricted to canonical quasi-coherent derived modules. -/
@[stacks 0H0R "derived sections on quasi-coherent objects"]
abbrev sections (X : C) :
    QC O ⥤ DerivedCategory (ModuleCat.{max (max u v) w} (O.1.obj (Opposite.op X))) :=
  ObjectProperty.ι (isQuasiCoherent O) ⋙ chaoticRGamma O X

/-- Lemma 21.43.4 (0H0R): when `X` is terminal,
derived sections at `X` identify canonical quasi-coherent derived modules with
`D(O(X))`. -/
@[stacks 0H0R]
theorem sections_isEquivalence
    (X : C) (hX : IsTerminal X) :
    (sections O X).IsEquivalence := sorry

/-- The canonical map on Hom sets induced by derived sections at `X`. -/
@[stacks 0H0S "canonical map on Hom sets"]
def homMap (X : C) (K : QC O)
    (M : DerivedCategory
      (ringedSiteModuleCategory.{u, v, max (max u v) w, max (max u v) w}
        (⊥ : GrothendieckTopology C) O)) :
    (K.obj ⟶ M) →
      ((chaoticRGamma O X).obj K.obj ⟶ (chaoticRGamma O X).obj M) :=
  (chaoticRGamma O X).map

/-- Lemma 21.43.5 (0H0S), terminal-object form: for a quasi-coherent source and an arbitrary
target, the canonical derived-sections map on Hom sets is bijective.  Applying this statement
to the slice category over `U` gives the objectwise form of the lemma. -/
@[stacks 0H0S]
theorem homMap_bijective
    (X : C) (hX : IsTerminal X)
    (K : QC O)
    (M : DerivedCategory
      (ringedSiteModuleCategory.{u, v, max (max u v) w, max (max u v) w}
        (⊥ : GrothendieckTopology C) O)) :
    Function.Bijective (homMap O X K M) := sorry

end CategoryTheory.ModulesOnCategory.Chaotic.Terminal
