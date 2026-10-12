/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Tor.FilteredColimit
import StacksCheckRecall

/-!
# Lemma 10.76.2

Filtered colimits in the first variable of `Tor` are handled by the reusable
`CategoryTheory.ModuleCat.Tor.preservesFilteredColimitsOfSize` instance.

@stack 0BNF
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

section

variable {R : Type u} [CommRing R]
variable {J : Type v} [Category.{v} J] [IsFiltered J]
variable [HasColimitsOfShape J (ModuleCat.{u} R)]
variable (F : J ⥤ ModuleCat.{u} R) (N : ModuleCat.{u} R) (n : ℕ)

/- Lemma 10.76.2: filtered colimits commute with `Torₙ(-, N)` for a fixed module `N`. -/
@[stacks 0BNF]
#check (inferInstance :
  IsIso (colimit.post F ((Tor (ModuleCat.{u} R) n).flip.obj N)))

#check (inferInstance :
  PreservesFilteredColimitsOfSize.{v, v}
    ((Tor (ModuleCat.{u} R) n).flip.obj N))

end
