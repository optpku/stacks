/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
import StacksCheckRecall

/-!
# Lemma 18.27.2

Compatibility facade for restriction of internal Hom to a slice site.  The
statement is the natural isomorphism owned by
`SheafOfModules.RingedSite.InternalHom.overNatIso`, with its objectwise
component exposed by `overComparisonIso`.

The ringed-site model supplies the canonical monoidal structures on the site
and its slice.  Closedness, the lax-monoidal restriction structure, and the
proof that its comparison maps are isomorphisms remain explicit coherent
hypotheses; no local instance or `sorry`-defined data is used here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})
variable (F G : ringedSiteModuleCategory J O) (U : C)
variable [HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [(SheafOfModules.overFunctor (ringSheaf J O) U).LaxMonoidal]
variable [CategoryTheory.Functor.LaxMonoidal.PreservesInternalHom
  (SheafOfModules.overFunctor (ringSheaf J O) U)]

/- Lemma 18.27.2 (0E8H): restriction to `C / U` commutes naturally with internal Hom. -/
@[stacks 0E8H]
#check (InternalHom.overNatIso O U F :
  ihom F ⋙ SheafOfModules.overFunctor (ringSheaf J O) U ≅
    SheafOfModules.overFunctor (ringSheaf J O) U ⋙ ihom (F.over U))

/- Its component at `G` is the source-facing isomorphism between the two internal-Hom
objects. -/
#check (InternalHom.overComparisonIso O U F G :
  ((ihom F).obj G).over U ≅ (ihom (F.over U)).obj (G.over U))

/- Before invertibility is used, the comparison is already an explicit canonical morphism. -/
#check (InternalHom.overComparison O U F G :
  ((ihom F).obj G).over U ⟶ (ihom (F.over U)).obj (G.over U))

end SheafOfModules.RingedSite
