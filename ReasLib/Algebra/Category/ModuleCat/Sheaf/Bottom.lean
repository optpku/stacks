module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.Tactic.CrossRefAttribute

/-!
# Modules on the bottom topology

Every presheaf is a sheaf for the bottom Grothendieck topology.  Thus modules over a ring
sheaf on that topology are canonically equivalent to modules over its underlying ring
presheaf.  This gives an Abelian structure without passing through sheafification or a
`WEqualsLocallyBijective` hypothesis.

@stack 091D
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace SheafOfModules.Bottom

variable {C : Type u} [Category.{v} C]

/-- The canonical equivalence between modules on the bottom topology and presheaves of
modules over the underlying ring presheaf. -/
@[stacks 091D "bottom-topology module equivalence"]
def equivalence (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{w}) :
    SheafOfModules.{z} R ≌ PresheafOfModules.{z} R.obj where
  functor := SheafOfModules.forget R
  inverse :=
    { obj := fun M => ⟨M, Presheaf.isSheaf_bot M.presheaf⟩
      map := fun f => ⟨f⟩ }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- Modules over a ring sheaf for the bottom topology form an Abelian category, via the
canonical equivalence with presheaves of modules. -/
@[stacks 091D "Abelian modules on the bottom topology"]
noncomputable instance abelian
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{w}) :
    Abelian (SheafOfModules.{z} R) :=
  abelianOfEquivalence (equivalence R).functor

end SheafOfModules.Bottom

end
