/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FilteredColimitExtension.Monoidal
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

/- Remark 56.4.2 (1): the tensor product of finitely presented modules is finitely
presented, so `Mod^fp` inherits the usual module-tensor monoidal structure. -/
@[stacks 0GP5] #check (ModuleCat.isFinitePresentation.instIsMonoidal :
  ∀ (A : Type u) [CommRing A],
    (ModuleCat.isFinitePresentation.{u, max u v} A).IsMonoidal)

/- Remark 56.4.2 (2): with `A`, `B`, `F`, and `F'` as in Lemma 56.4.1, the usual tensor
product of modules makes `Mod^fp_A`, `Mod^fp_B`, `Mod_A`, and `Mod_B` monoidal, and
if `F` is monoidal then so is any filtered-colimit-preserving extension `F'`
isomorphic to `F` on finitely presented modules.

The restriction isomorphism `e` is a noncanonical explicit parameter, so this
monoidal structure is a named `def` rather than a global `instance`. -/
@[stacks 0GP5] #check (ModuleCat.fpFilteredColimitExtension_monoidal :
  ∀ {A : Type u} [CommRing A] {B : Type v} [CommRing B]
    (F : (ModuleCat.isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (ModuleCat.isFinitePresentation.{v, max u v} B).FullSubcategory)
    [F.Monoidal]
    (F' : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B)
    (e : (ModuleCat.isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅
      F ⋙ (ModuleCat.isFinitePresentation.{v, max u v} B).ι)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F'], F'.Monoidal)
